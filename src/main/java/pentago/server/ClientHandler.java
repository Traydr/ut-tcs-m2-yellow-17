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
    private boolean helloPassed;
    private boolean loggedIn;
    public ArrayList<String> clientSupportedFeatures;
    private Game game;

    /**
     * A constructor for the client handler object.
     *
     * @param socket The socket that is connected to a user
     * @param server The server object
     * @throws IOException
     */
    public ClientHandler(Socket socket, SimplePentagoServer server) throws IOException {
        this.socket = socket;
        this.server = server;
        this.writer = new BufferedWriter(new OutputStreamWriter(this.socket.getOutputStream()));
        this.helloPassed = false;
        this.loggedIn = false;
        this.clientSupportedFeatures = new ArrayList<>();
    }

    /**
     * Returns the username of the client.
     *
     * @return username
     */
    public String getUsername() {
        return username;
    }

    /**
     * Sets a new game objects.
     *
     * @param game
     */
    public void setGame(Game game) {
        this.game = game;
    }

    /**
     * Ends the game by turning this into a null reference.
     */
    public void endGame() {
        this.game = null;
    }

    /**
     * Sends a message to this specific client.
     *
     * @param message the message to be sent to the client
     */
    public void sendMessage(String message) {
        try {
            if (!this.socket.isClosed()) {
                this.writer.write(message + "\n");
                this.writer.flush();
                return;
            }
            close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * Sends a message with the "ERROR~" prefix.
     *
     * @param message error message to be sent
     */
    public void sendError(String message) {
        sendMessage("ERROR~" + message);
        close();
    }

    /**
     * Closes the connection with the client, if the user was in a game it sends a win by.
     * disconnect
     */
    public void close() {
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
        }
    }

    /**
     * Parses the data received from the client.
     *
     * @param input String of chars received from the user
     */
    private void parseClient(String input) {
        String[] parsedInput = input.split("~");

        switch (parsedInput[0]) {
            case "HELLO":
                // Receiving the HELLO
                if (helloPassed) {
                    sendError("Unexpected [HELLO]");
                    break;
                } else if (parsedInput.length < 2) {
                    sendError("Too few arguments");
                    break;
                }

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
                if (parsedInput.length != 2) {
                    System.out.println(Arrays.toString(parsedInput));
                    sendError("Login: too many or too few arguments");
                    break;
                } else if (loggedIn || server.isUsernameInUse(parsedInput[1], this)) {
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
                server.addToQueue(this);
                server.startNewGame();
                break;
            case "MOVE":
                if (parsedInput.length != 3) {
                    sendError("Move: too many or too few arguments");
                    break;
                }

                int move = Integer.parseInt(parsedInput[1]);
                int rotate = Integer.parseInt(parsedInput[2]);

                if (move < 0 || move > 35 || rotate < 0 || rotate > 8) {
                    sendError("Move or rotate have invalid numbers");
                    close();
                    break;
                }

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
                sendError("ERROR~Unrecognised command: " + parsedInput[0]);
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
