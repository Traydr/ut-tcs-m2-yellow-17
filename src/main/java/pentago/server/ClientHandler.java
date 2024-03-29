package pentago.server;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Scanner;

public class ClientHandler implements Runnable {
    private Socket socket;
    private SimplePentagoServer server;
    private String username;
    private BufferedWriter writer;
    public ArrayList<String> clientSupportedFeatures;
    private Game game;
    private boolean helloPassed;
    private boolean loggedIn;
    private boolean hasSentNewGame;
    private boolean isClosed;

    /**
     * A constructor for the client handler object.
     *
     * @param socket The socket that is connected to a user
     * @param server The server object
     * @throws IOException Exception thrown if the socket could not get an output stream
     */
    //@ requires socket != null;
    //@ requires server != null;
    //@ ensures this.helloPassed == false && this.loggedIn == false && this.hasSentNewGame == false;
    //@ ensures this.isClosed == false;
    public ClientHandler(Socket socket, SimplePentagoServer server) throws IOException {
        this.socket = socket;
        this.server = server;
        this.writer = new BufferedWriter(new OutputStreamWriter(this.socket.getOutputStream()));
        this.clientSupportedFeatures = new ArrayList<>();
        this.helloPassed = false;
        this.loggedIn = false;
        this.hasSentNewGame = false;
        this.isClosed = false;
    }

    /**
     * Returns the username of the client.
     *
     * @return username
     */
    //@ requires this.username != null;
    //@ ensures \result == this.username;
    public String getUsername() {
        return username;
    }

    /**
     * Returns if the new game message has been sent yet.
     *
     * @return true if so, false if otherwise
     */
    //@ requires hasSentNewGame == true || isHasSentNewGame() == false;
    //@ ensures \result == hasSentNewGame;
    public boolean isHasSentNewGame() {
        return hasSentNewGame;
    }

    /**
     * Set has set new game.
     *
     * @param input true if message has been sent, false otherwise
     */
    //@ requires input == true || input == false;
    //@ ensures this.hasSentNewGame == input;
    public void setHasSentNewGame(boolean input) {
        this.hasSentNewGame = input;
    }

    /**
     * Returns true if the client is already in another game.
     *
     * @return true if already in a game
     */
    //@ ensures \result == false || \result == true;
    public boolean isAlreadyInGame() {
        return game != null;
    }

    /**
     * Sets a new game objects.
     *
     * @param game Game object
     */
    //@ requires game != null;
    //@ ensures this.game == game;
    public void setGame(Game game) {
        this.game = game;
    }

    /**
     * Ends the game by turning this into a null reference.
     */
    //@ ensures this.game == null;
    public void endGame() {
        this.game = null;
    }

    /**
     * Sends a message to this specific client.
     *
     * @param message the message to be sent to the client
     */
    //@ requires message != null;
    public void sendMessage(String message) {
        try {
            if (!this.socket.isClosed()) {
                this.writer.write(message + "\n");
                this.writer.flush();
                return;
            }
            close();
        } catch (IOException e) {
            System.out.println();
            close();
        }
    }

    /**
     * Sends a message with the "ERROR~" prefix.
     *
     * @param message error message to be sent
     */
    //@ requires message != null;
    public void sendError(String message) {
        sendMessage("ERROR~" + message);
        close();
    }

    /**
     * Closes the connection with the client, if the user was in a game it sends a win by.
     * disconnect
     */
    //@ ensures socket.isClosed() && !server.isUsernameInUse(this.username, this);
    //@ ensures game == null;
    public void close() {
        if (isClosed) {
            return;
        }

        try {
            if (!socket.isClosed()) {
                socket.close();
            }

            if (game != null) {
                game.winByDisconnect(this);
            }
        } catch (IOException e) {
            e.printStackTrace();
        } finally {
            server.removeClient(this);
            isClosed = true;
        }
    }

    /**
     * Parses the data received from the client.
     *
     * @param input String of chars received from the user
     */
    //@ requires input != null;
    private void parseClient(String input) {
        String[] parsedInput = input.split("~");

        switch (parsedInput[0]) {
            case "HELLO":
                // Check if we have already received a hello
                if (helloPassed) {
                    sendError("Unexpected [HELLO]");
                    break;
                } else if (parsedInput.length < 2) {
                    // Check to make sure that there are enough args
                    sendError("Too few arguments");
                    break;
                }

                // If there are more than 2 args then
                // these must be the features of the connecting client
                if (parsedInput.length > 2) {
                    for (int i = 2; i < parsedInput.length; i++) {
                        clientSupportedFeatures.add(parsedInput[i]);
                    }
                }

                // Sending back HELLO
                String features = "";
                for (String feature : server.getSupportedFeatures()) {
                    features += "~" + feature;
                }
                sendMessage("HELLO~" + server.getServerName() + features);
                break;
            case "LOGIN":
                // Check that there are exactly 2 arguments
                if (parsedInput.length != 2) {
                    System.out.println(Arrays.toString(parsedInput));
                    sendError("Login: too many or too few arguments");
                    break;
                } else if (loggedIn || server.isUsernameInUse(parsedInput[1], this)) {
                    // If the user gas already logged in or
                    // there is a username already in use by another client
                    sendMessage("ALREADYLOGGEDIN");
                    break;
                }
                username = parsedInput[1];
                sendMessage("LOGIN");
                break;
            case "LIST":
                List<String> allUsernames = server.getAllUsernames();
                String output = "LIST";
                for (String name : allUsernames) {
                    output += "~" + name;
                }
                sendMessage(output);
                break;
            case "QUEUE":
                // Adds to queue and attempts to start a new game if
                // there are enough client in queue
                server.addToQueue(this);
                server.startNewGame();
                break;
            case "MOVE":
                // Check that there are exactly the correct amount of arguments
                if (parsedInput.length != 3) {
                    sendError("Move: too many or too few arguments");
                    break;
                }

                int move = Integer.parseInt(parsedInput[1]);
                int rotate = Integer.parseInt(parsedInput[2]);

                // Check to make sure the moves received are valid
                if (move < 0 || move > 35 || rotate < 0 || rotate > 8) {
                    sendError("Move or rotate have invalid numbers");
                    break;
                }

                // If the client is not currently in a game
                if (game == null) {
                    sendError("There is no game");
                    break;
                }

                // Sets the move, but sends back an error if the move is invalid
                if (!game.setBoard(move, rotate, this)) {
                    sendError("It is not your turn");
                    break;
                }
                break;
            case "PING":
                sendMessage("PONG");
                break;
            case "PONG":
                // TODO Implement time out?
                break;
            case "CHAT":
                if (parsedInput.length != 2) {
                    sendError("Chat: too many or too few arguments");
                }
                server.sendChat(this, parsedInput[1]);
                break;
            case "WHISPER":
                if (parsedInput.length != 3) {
                    sendError("Whisper: too many or too few arguments");
                }
                server.sendWhisper(this, parsedInput[1], parsedInput[2]);
                break;
            case "QUIT":
                close();
                break;
            default:
                sendError("Unrecognised command: " + parsedInput[0]);
                break;
        }
    }

    /**
     * Adds the client to the server, keeps reading from the socket until it is closed.
     */
    @Override
    public void run() {
        server.addClient(this);
        try (Scanner scanner = new Scanner(new InputStreamReader(this.socket.getInputStream()))) {
            String input;
            while (scanner.hasNextLine()) {
                input = scanner.nextLine();
                parseClient(input);
            }
        } catch (IOException e) {
            e.printStackTrace();
        } finally {
            close();
        }

    }
}
