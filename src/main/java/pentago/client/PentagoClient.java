package pentago.client;

import pentago.client.player.Bot;
import pentago.client.player.Human;
import pentago.client.player.Player;
import pentago.client.player.SmartStrategy;
import pentago.game_logic.Board;
import pentago.game_logic.CommandParser;
import pentago.game_logic.Mark;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class PentagoClient {
    private String serverAddress;
    private int port;
    private Network network;
    private Game game;
    private ArrayList<String> serverFeatures;
    private Player player;
    private String moveCmd;
    private int moveCounter = 0;
    private boolean isValidName = false;
    private boolean autoQueue = false;

    /**
     * Constructor for a new PentagoClient object.
     *
     * @param serverAddress The ip address for the server
     * @param port          The port the server is running on
     * @param player        The type of player that is playing it
     */
    public PentagoClient(String serverAddress, int port, Player player) {
        this.serverAddress = serverAddress;
        this.port = port;
        this.network = new Networking();
        this.serverFeatures = new ArrayList<>();
        this.player = player;
    }

    /**
     * Constructor for a PentagoClient object that connects to the reference server.
     *
     * @param player The type of player that is playing it
     */
    public PentagoClient(Player player) {
        this("0.0.0.0", 8080, player);
    }

    /**
     * Main function where the user specifies how the user wants to play. What the username should
     * be, what ip address and port do they want to connect to,
     *
     * @param args Some arguments for the default start of the program
     */
    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        PentagoClient client;
        Player player;

        // Goes through the command line arguments to see what presets it should use
        // if no preset has been picked then it will ask the user to pick
        List argsList = Arrays.asList(args);
        if (argsList.contains("--human")) {
            System.out.println("Player: Human");
            player = new Human("Human", Mark.BLACK);
        } else if (argsList.contains("--naive-bot")) {
            System.out.println("Player: Naive bot");
            player = new Bot(Mark.BLACK);
        } else if (argsList.contains("--smart-bot")) {
            System.out.println("Player: Smart bot");
            player = new Bot(Mark.BLACK, new SmartStrategy());
        } else {
            System.out.println("(H)uman, (B)ot or (S)mart bot");
            String input = scanner.nextLine();
            if (input.equals("B")) {
                player = new Bot(Mark.BLACK);
                System.out.println("Player: Naive bot");
            } else if (input.equals("S")) {
                player = new Bot(Mark.BLACK, new SmartStrategy());
                System.out.println("Player: Smart bot");
            } else {
                player = new Human("Human", Mark.BLACK);
                System.out.println("Player: Human");
            }
        }

        // if the --preset command line argument is given it will connect to the reference server
        // otherwise it asks the user to choose
        if (argsList.contains("--preset")) {
            Random random = new Random();
            client = new PentagoClient(player);
        } else {
            System.out.println("(P)reset or (C)ustom?");
            if (scanner.nextLine().equals("C")) {
                System.out.println("Server Address:");
                String serverAddress = scanner.nextLine();
                System.out.println("Server Port:");
                int port = Integer.parseInt(scanner.nextLine());

                client = new PentagoClient(serverAddress, port, player);

            } else {
                Random random = new Random();
                client = new PentagoClient(player);
            }
        }

        // Asks the user to enter a name, will keep asking until the user enters an invalid name
        System.out.println("Username:");
        String username = scanner.nextLine();

        while (username.contains("~")) {
            System.out.println("ERR: invalid username cannot contain \"~\" characters" +
                               "\nPlease try again:");
            username = scanner.nextLine();
        }

        // Sets the username
        player.setName(username);

        // Tries to connect if it doesn't work then it exits
        try {
            if (!client.network.connect(
                    InetAddress.getByName(client.serverAddress), client.port, client)) {
                System.out.println("ERR: bad connection");
                System.exit(1);
            }
        } catch (UnknownHostException exception) {
            System.out.println("ERR: no connection");
            System.exit(2);
        }

        // Connects to the server and displays the help menu
        client.connectToServer();
        client.displayHelp();
        String output;
        // Reads from system in until quit is received
        // Does not allow ~ characters in input
        while (scanner.hasNextLine() && client.network != null) {
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

        // Closes everything before quiting
        client.network.close();
        scanner.close();
        System.out.println("Quitting!");
    }

    /**
     * Returns the server address.
     *
     * @return server address as string
     */
    public String getServerAddress() {
        return serverAddress;
    }

    /**
     * Returns port to connect to.
     *
     * @return integer port
     */
    public int getPort() {
        return port;
    }

    /**
     * Returns the network object.
     *
     * @return network object
     */
    public Network getNetwork() {
        return network;
    }

    /**
     * Returns the game object.
     *
     * @return Game object
     */
    public Game getGame() {
        return game;
    }

    /**
     * Returns player object.
     *
     * @return Player object
     */
    public Player getPlayer() {
        return player;
    }

    /**
     * Returns the current move counter for a game.
     *
     * @return counter
     */
    public int getMoveCounter() {
        return moveCounter;
    }

    /**
     * Sets the move counter to a specific value.
     *
     * @param moveCounter sets the value of the move counter
     */
    public void setMoveCounter(int moveCounter) {
        this.moveCounter = moveCounter;
    }

    /**
     * Sets whether the selected username is valid.
     *
     * @param validName true if valid, otherwise false
     */
    public void setValidName(boolean validName) {
        isValidName = validName;
    }

    /**
     * Starts a new game for the client side code to keep track of.
     *
     * @param player1 Player 1 name
     * @param player2 Player 2 name
     */
    public void startNewGame(String player1, String player2) {
        // Starts the game with fake players, sets their names to the actual player names
        Player humanPlayer1 = new Human(player1, Mark.WHITE);
        Player humanPlayer2 = new Human(player2, Mark.BLACK);
        this.game = new Game(humanPlayer1, humanPlayer2);
    }

    /**
     * Ends the current game.
     */
    public void endCurrentGame() {
        this.game = null;
    }

    /**
     * Performs the first time connect to the server.
     */
    public void connectToServer() {
        network.sendMessage("HELLO~" + player.getName() + "~CHAT");
        this.login();
    }

    /**
     * Logs in to the server.
     */
    public void login() {
        network.sendMessage("LOGIN~" + player.getName());
        this.isValidName = true;
    }

    /**
     * Parses the input from the user and translates it into commands.
     *
     * @param input user input
     */
    private void parseInput(String input) {
        String[] parsedInput = input.split(" ");
        if (!isValidName && !parsedInput[0].equals("setname")) {
            System.out.println("Expected [setname] command. Please set a name before continuing");
            return;
        }
        switch (parsedInput[0]) {
            case "help":
                displayHelp();
                break;
            case "list":
                network.sendMessage("LIST");
                break;
            case "place":
                // If a place has been done before then we do not allow the user to place again
                // Also if there are not exactly 2 arguments that being 'place A0' then we do not
                // accept the command either
                if (moveCmd != null) {
                    System.out.println("ERR: cannot place twice");
                    break;
                } else if (parsedInput.length != 2) {
                    System.out.println("ERR: too many or too few arguments");
                    break;
                }

                // If it not our turn then we break aswell
                if (moveCounter % 2 == 0) {
                    System.out.println("It is not your turn!");
                    break;
                }

                // We check if the move is valid according to the system we use
                Pattern movePattern = Pattern.compile("[A-D][0-8]");
                Matcher moveMatcher = movePattern.matcher(parsedInput[1]);
                boolean isValidMove = moveMatcher.find();
                if (!isValidMove) {
                    System.out.println("This is not a valid move");
                    break;
                }

                //Then we check if there is already a move there
                if (this.game.getBoard().getField(parsedInput[1]) != Mark.EMPTY) {
                    System.out.println("There is already a mark there");
                    break;
                }
                // Finally, we commit the move to moveCmd var
                Board tmpBoard = new Board();
                int[] coords = tmpBoard.getCoords(parsedInput[1]);
                moveCmd = "MOVE~" +
                          CommandParser.localToProtocolCoords(coords[0], coords[1], coords[2]);
                break;
            case "rotate":
                // Check if there has been anything placed yet and that there are only 2 arguments
                if (moveCmd == null) {
                    System.out.println("ERR: nothing has been placed yet");
                    break;
                } else if (parsedInput.length != 2) {
                    System.out.println("ERR: too many or too few arguments");
                    break;
                }

                // Check that the move is in the right pattern
                Pattern rotatePattern = Pattern.compile("[A-D][L|R]");
                Matcher rotateMatcher = rotatePattern.matcher(parsedInput[1]);
                boolean isValidRotate = rotateMatcher.find();
                if (!isValidRotate) {
                    System.out.println("This is not a valid rotation command");
                    break;
                }

                // Finally, send the move and wipe moveCmd
                moveCmd += "~" + CommandParser.localToProtocolRotate(parsedInput[1]);
                network.sendMessage(moveCmd);
                moveCmd = null;
                break;
            case "rplace":
                // Reset moveCmd if the player didn't want to place there
                moveCmd = "";
                break;
            case "setname":
                // Sets a new username and tries to re log
                player.setName(parsedInput[1]);
                this.login();
                break;
            case "ping":
                network.sendMessage("PING");
                break;
            case "queue":
                network.sendMessage("QUEUE");
                break;
            case "chat":
                // If the server doesn't support chatting or there is no message break
                if (!serverFeatures.contains("CHAT")) {
                    System.out.println("ERR: The server does not support chatting");
                }
                if (parsedInput.length == 1) {
                    System.out.println("ERR: no chat message");
                    break;
                }
                String tmpChat = "";
                for (int i = 1; i < parsedInput.length; i++) {
                    tmpChat += parsedInput[i] + " ";
                }
                network.sendMessage("CHAT~" + tmpChat);
                break;
            case "whisper":
                // Checks to make sure that the server supports chatting
                if (!serverFeatures.contains("CHAT")) {
                    System.out.println("ERR: The server does not support chatting");
                }
                // Checks to make sure that the whisper has the correct amount of details
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
                // Gives a random move if currently in a game
                if (game == null) {
                    System.out.println("ERR: There is no game");
                    break;
                }
                System.out.println(game.getRandomMove());
                break;
            case "show":
                // shows the board with a help board aswell
                if (game == null) {
                    System.out.println("ERR: There is no game");
                    break;
                }
                System.out.println(game.update(true));
                break;
            case "autoqueue":
                // toggles auto queue
                autoQueue = !autoQueue;
                break;
            default:
                System.out.println("Unknown Command: " + parsedInput[0]);
                break;
        }
    }

    public boolean isAutoQueue() {
        return autoQueue;
    }

    /**
     * Makes a bot do a move and then sends it to the server.
     */
    public void makePlayerDoMove() {
        // Makes a bot do a move and then sends it to the server
        Bot bot = new Bot(this.player.getMark(), this.player.getStrategy());
        String[] move = bot.determineMove(this.game.getBoard());
        int[] coords = game.getBoard().getCoords(move[0]);
        int place = CommandParser.localToProtocolCoords(coords[0], coords[1], coords[2]);
        int rotate = CommandParser.localToProtocolRotate(move[1]);

        network.sendMessage("MOVE~" + place + "~" + rotate);
    }

    /**
     * Displays the help message to the user.
     */
    public void displayHelp() {
        String[] commands = {"list\n\tLists all users currently connected to the server",
                             "queue\n\tQueues up for a new game",
                             "place [A-D][0-8]\n\tPlaces a piece down a piece on the position",
                             "rotate [A-D][L|R]\n\tRotates a quadrant in a specific direction",
                             "ping\n\tPings the server to see if its still alive",
                             "chat [message]" + (this.serverFeatures.contains("CHAT") ? "" :
                                                 " (Not supported by this server)") +
                             "\n\tsends a message to everyone on the server",
                             "whisper [user] [message]" +
                             (this.serverFeatures.contains("CHAT") ? "" :
                              "(Not supported by this server)") +
                             "\n\tsends a message to a specific person",
                             "help\n\tDisplays this help message",
                             "hint\n\tDisplays a possible move",
                             "show\n\tShows the current state of the board ",
                             "autoqueue\n\tToggles the autoqueue",
                             "quit\n\tquits out of the program"};


        String output = "Commands:";
        for (String command : commands) {
            output += "\n" + command;
        }
        System.out.println(output);
    }

    /**
     * Adds a server feature the list of server features.
     *
     * @param feature name of a feature
     */
    public void addServerFeature(String feature) {
        this.serverFeatures.add(feature);
    }
}
