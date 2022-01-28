package pentago.server;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

public class ClientHandler implements Runnable {
    private Socket socket;
    private SimplePentagoServer server;
    private String username;
    private BufferedWriter writer;
    private boolean helloPased;
    private boolean loggedIn;
    private String serverName;
    private ArrayList<String> supportedFeatures;

    public ClientHandler(Socket socket, SimplePentagoServer server) throws IOException {
        this.socket = socket;
        this.server = server;
        this.writer = new BufferedWriter(new OutputStreamWriter(this.socket.getOutputStream()));
        helloPased = false;
        loggedIn = false;

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

    public void sendMessage(String message) {
        try {
            this.writer.write(message + "\n");
            this.writer.flush();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public void sendError(String message) {
        sendMessage("ERROR~" + message);
    }

    public void close() {
        try {
            if (!socket.isClosed()) {
                socket.close();
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
                if (helloPased) {
                    sendError("Unexpected [HELLO]");
                    close();
                    break;
                }
                String features = "";
                for (String feature : supportedFeatures) {
                    features += "~" + feature;
                }
                sendMessage("HELLO~" + serverName + features);
                break;
            case "LOGIN":
                if (parsedInput.length != 2) {
                    sendError("Too many or too few arguments");
                    break;
                } else if (loggedIn || server.isUsernameInUse(parsedInput[1])) {
                    sendMessage("ALREADYLOGGEDIN");
                    close();
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
                break;
            case "MOVE":
                // TODO Implement movement
                break;
            case "PING":
                sendMessage("PONG");
                break;
            case "PONG":
                // TODO Implement time out?
                break;
            case "CHAT":
                if (parsedInput.length != 2) {
                    sendMessage("ERROR~Too many or too few arguments");
                }
                server.sendChat(this, parsedInput[1]);
                break;
            case "WHISPER":
                if (parsedInput.length != 3) {
                    sendMessage("ERROR~Too many or too few arguments");
                }
                server.sendWhisper(this, parsedInput[1], parsedInput[2]);
                break;
            case "QUIT":
                close();
                break;
            default:
                sendMessage("ERROR~Unrecognised command: " + parsedInput[0]);
                break;
        }
    }

    @Override
    public void run() {
        server.addClient(this);
        try (Scanner scanner = new Scanner(new InputStreamReader(this.socket.getInputStream()))) {
            // Read HELLO and LOGIN

            String input;
            while (scanner.hasNextLine()) {
                input = scanner.nextLine();
                // TODO parse input
            }
        } catch (IOException e) {
            e.printStackTrace();
        } finally {
            close();
        }

    }
}
