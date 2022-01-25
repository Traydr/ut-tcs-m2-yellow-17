package pentago.client;

import pentago.client.player.Human;
import pentago.client.player.Player;
import pentago.game_logic.Board;
import pentago.game_logic.CommandParser;
import pentago.game_logic.Mark;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.Random;
import java.util.Scanner;

public class PentagoClient {
    public String serverAddress;
    public int port;
    public String username;
    public Network network;
    public Game game;
    public ArrayList<String> serverFeatures;
    public Player player;
    public String moveCmd;

    public PentagoClient(String serverAddress, int port, String username) {
        this.serverAddress = serverAddress;
        this.port = port;
        this.username = username;
        this.network = new Networking();
        this.serverFeatures = new ArrayList<>();
    }

    public PentagoClient(int randNum) {
        this("130.89.253.64", 55555, "Default-Username-Tray" + randNum);
    }

    //TODO Save the features of the server
    //TODO Make sure client can only do the functions of the server
    //TODO Let person choose to if they either want a bot or human to play
    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        PentagoClient client;

        System.out.println("(P)reset or (C)ustom?");
        if (scanner.nextLine().equals("C")) {
            System.out.println("Server Address:");
            String serverAddress = scanner.nextLine();
            System.out.println("Server Port:");
            int port = scanner.nextInt();

            System.out.println("Username:");
            String username = scanner.nextLine();

            while (username.contains("~")) {
                System.out.println("ERR: invalid username cannot contain \"~\" characters" +
                                   "\nPlease try again:");
                username = scanner.nextLine();
            }

            client = new PentagoClient(serverAddress, port, username);

        } else {
            Random random = new Random();
            client = new PentagoClient(random.nextInt(999999));
        }

        try {
            if (!client.network.connect(
                    InetAddress.getByName(client.serverAddress), client.port, client)) {
                System.out.println("ERR: bad connection");
                System.exit(1);
            }
        } catch (UnknownHostException e) {
            System.out.println("ERR: no connection");
            System.exit(2);
        }

        client.connectToServer(client.username);

        String output;
        while (scanner.hasNextLine()) {
            output = scanner.nextLine();
            if (output.equals("quit")) {
                break;
            } else if (output.contains("~")) {
                System.out.println("\nInput cannot contain \"~\" characters");
                continue;
            } else {
                client.parseInput(output);
            }
        }

        scanner.close();
    }

    public void startNewGame(String player1, String player2) {
        // TODO Redo this
        // TODO Make a network player probably
        Player humanPlayer1 = new Human(player1, Mark.WHITE);
        Player humanPlayer2 = new Human(player2, Mark.BLACK);
        this.game = new Game(humanPlayer1, humanPlayer2);
    }

    public void endCurrentGame() {
        this.game = null;
    }

    public void connectToServer(String username) {
        network.sendMessage("HELLO~" + username + "~CHAT");
        network.sendMessage("LOGIN~" + username);
    }

    public void parseInput(String input) {
        String[] parsedInput = input.split(" ");
        switch (parsedInput[0]) {
            case "help":
                displayHelp();
                break;
            case "list":
                network.sendMessage("LIST");
                break;
            case "place": // TODO figure out how to move, store the move and rotate somewhere?
                if (moveCmd != null) {
                    System.out.println("ERR: cannot place twice");
                    break;
                } else if (parsedInput.length != 2) {
                    System.out.println("ERR: too many or too few arguments");
                    break;
                }
                Board tmpBoard = new Board();
                int[] coords = tmpBoard.getCoords(parsedInput[1]);
                moveCmd = "MOVE~" +
                          CommandParser.localToProtocolCoords(coords[0], coords[1], coords[2]);
                break;
            case "rotate":
                if (moveCmd == null) {
                    System.out.println("ERR: nothing has been placed yet");
                    break;
                } else if (parsedInput.length != 2) {
                    System.out.println("ERR: too many or too few arguments");
                    break;
                    //                } else if (moveCmd.length() != 7) {
                    //                    System.out.println("ERR: Place command invalid, please
                    //                    reset [rplace]");
                    //                    break;
                }
                moveCmd += "~" + CommandParser.localToProtocolRotate(parsedInput[1]);
                network.sendMessage(moveCmd);
                moveCmd = null;
                break;
            case "rplace":
                moveCmd = "";
                break;
            case "ping":
                network.sendMessage("PING");
                break;
            case "queue":
                network.sendMessage("QUEUE");
                break;
            case "chat":
                if (parsedInput.length == 1) {
                    System.out.println("ERR: no chat message");
                    break;
                }
                String tmpChat = "";
                for (int i = 1; i < parsedInput.length; i++) {
                    tmpChat += " " + parsedInput[i];
                }
                network.sendMessage("CHAT~" + tmpChat);
                break;
            case "whisper":
                if (parsedInput.length < 3) {
                    System.out.println("ERR: no whisper message / or no username specified");
                    break;
                }
                String tmpWhisper = "";
                for (int i = 2; i < parsedInput.length; i++) {
                    tmpWhisper += " " + parsedInput[i];
                }
                network.sendMessage(String.format("WHISPER~%s~%s", parsedInput[1], tmpWhisper));
                break;
            case "hint":
                if (game == null) {
                    System.out.println("ERR: There is no game");
                    break;
                }
                System.out.println(game.getRandomMove());
                break;
            case "show":
                if (game == null) {
                    System.out.println("ERR: There is no game");
                    break;
                }
                System.out.println(game.update());
                break;
            default:
                //Debug for now
                //network.sendMessage(input);
                System.out.println("Unknown Command: " + parsedInput[0]);
                break;
        }
    }

    public void displayHelp() {
        //TODO Format this to look nicer
        String[] commands = {"list\n\tLists all users currently connected to the server",
                             "queue\n\tQueues up for a new game",
                             "move [A-D][0-8]\n\tPlaces a piece down a piece on the position",
                             "rotate [A-D][L|R]\n\tRotates a quadrant in a specific direction",
                             "ping\n\tPings the server to see if its still alive",
                             "chat [message]\n\tsends a message to everyone on the server",
                             "whisper [user] [message]\n\tsends a message to a specific person",
                             "help\n\tDisplays this help message",
                             "hint\n\tDisplays a possible move",
                             "show\n\tShows the current state of the board ",
                             "quit\n\tquits out of the program"};

        String output = "Commands:";
        for (String command : commands) {
            output += "\n" + command;
        }
        System.out.println(output);
    }
}
