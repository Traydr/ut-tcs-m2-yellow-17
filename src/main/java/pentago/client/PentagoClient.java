package pentago.client;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.Scanner;

public class PentagoClient {
    public String serverAddress;
    public int port;
    public String username;
    public Network network;
    public Game game;
    public ArrayList<String> serverFeatures;

    public PentagoClient(String serverAddress, int port, String username) {
        this.serverAddress = serverAddress;
        this.port = port;
        this.username = username;
        this.network = new Networking();
        this.serverFeatures = new ArrayList<>();
    }

    public PentagoClient() {
        this("130.89.253.64", 55555, "Default-Username-Tray");
    }

    //TODO Save the features of the server
    //TODO Make sure client can only do the functions of the server
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
                System.out.println("ERR: Invalid username cannot contain \"~\" characters" +
                                   "\nPlease try again:");
                username = scanner.nextLine();
            }

            client = new PentagoClient(serverAddress, port, username);

        } else {
            client = new PentagoClient();
        }

        try {
            if (!client.network.connect(InetAddress.getByName(client.serverAddress), client.port)) {
                System.out.println("ERR: BAD CONNECTION");
            }
        } catch (UnknownHostException e) {
            e.printStackTrace();
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
            case "move": // TODO figure out how to move, store the move and rotate somewhere?
                break;
            case "rotate":
                break;
            case "ping":
                network.sendMessage("PING");
                break;
            case "queue":
                network.sendMessage("QUEUE");
                break;
            case "chat":
                String tmp = "";
                for (int i = 1; i < parsedInput.length; i++) {
                    tmp += " " + parsedInput[i];
                }
                network.sendMessage("CHAT~" + tmp);
                break;
            default:
                //Debug for now
                network.sendMessage(input);
                //System.out.println("Unknown Command: " + parsedInput[0]);
                break;
        }
    }

    public void displayHelp() {
        //TODO Format this to look nicer
        String[] commands = {"list - Lists all users currently connected to the server",
                             "queue - Queues up for a new game",
                             "move [A-D][0-8] - Places a piece down a piece on the position",
                             "rotate [A-D][L|R] - Rotates a quadrant in a specific direction",
                             "ping - Pings the server to see if its still alive",
                             "chat - sends a message to everyone on the server",
                             "whisper - sends a message to a specific person on the server",
                             "help - Displays this help message",
                             "quit - quits out of the program"};

        String output = "Commands:";
        for (String command : commands) {
            output += "\n" + command;
        }
        System.out.println(output);
    }
}
