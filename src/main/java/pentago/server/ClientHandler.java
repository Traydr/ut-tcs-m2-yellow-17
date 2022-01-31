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

// TODO Cleanup the class and make it more structured
public class ClientHandler implements Runnable {
    private Socket socket;
    private SimplePentagoServer server;
    private String username;
    private BufferedWriter writer;
    private boolean helloPased;
    private boolean loggedIn;
    private String serverName;
    private ArrayList<String> supportedFeatures;
    private ArrayList<String> clientSupportedFeatures;
    private Game game;

    public ClientHandler(Socket socket, SimplePentagoServer server) throws IOException {
        this.socket = socket;
        this.server = server;
        this.writer = new BufferedWriter(new OutputStreamWriter(this.socket.getOutputStream()));
        helloPased = false;
        loggedIn = false;
        clientSupportedFeatures = new ArrayList<>();

        // TODO Decide where to place server name & how features are handled
        // <---------- DEBUG ---------->
        serverName = "TestServer";
        supportedFeatures = new ArrayList<>();
        supportedFeatures.add("CHAT");
        // <---------- DEBUG ---------->
    }

    public String getUsername() {
        return username;
    }

    public void setGame(Game game) {
        this.game = game;
    }

    public void endGame() {
        this.game = null;
    }

    public void sendMessage(String message) {
        try {
            if (!this.socket.isClosed()) {
                this.writer.write(message + "\n");
                this.writer.flush();
                return;
            }
            game.checkWinner();
            close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public void sendError(String message) {
        sendMessage("ERROR~" + message);
        close();
    }

    public void close() {
        try {
            if (!socket.isClosed()) {
                socket.close();
            }

            if (game != null) {
                //TODO win game by disconnect
            }
        } catch (IOException e) {
            e.printStackTrace();
        } finally {
            server.removeClient(this);
        }
    }

    public void parseClient(String input) {
        String[] parsedInput = input.split("~");

        switch (parsedInput[0]) {
            case "HELLO":
                // Receiving the HELLO
                if (helloPased) {
                    sendError("Unexpected [HELLO]");
                    break;
                } else if (parsedInput.length <= 2) {
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
                for (String feature : supportedFeatures) {
                    features += "~" + feature;
                }
                sendMessage("HELLO~" + serverName + features);
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

                game.checkWinner();
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
