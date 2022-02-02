package pentago.client;

import pentago.client.player.Bot;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.Socket;

public class Listener implements Runnable {
    private Socket socket;
    private BufferedReader br = null;
    private Network network;
    private PentagoClient client;

    /**
     * Constructs a new listener object.
     *
     * @param sock   the socket connecting to the server
     * @param net    the network object
     * @param client the client object
     */
    Listener(Socket sock, Network net, PentagoClient client) {
        this.socket = sock;
        this.network = net;
        this.client = client;
        try {
            this.br = new BufferedReader(new InputStreamReader(this.socket.getInputStream()));
        } catch (IOException e) {
            e.printStackTrace();
        }
        this.client.setMoveCounter(0);
    }

    /**
     * Closes the listener by closing the buffered reader.
     */
    void close() {
        try {
            br.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * Parses the messages from the server.
     *
     * @param input protocol messages from the server
     */
    private void messageParser(String input) {
        String[] inputParsed = input.split("~");

        switch (inputParsed[0]) {
            case "HELLO":
                StringBuilder features = new StringBuilder();
                for (int i = 2; i < inputParsed.length; i++) {
                    features.append("\n\t").append(inputParsed[i]);
                    client.addServerFeature(inputParsed[i]);
                }
                System.out.println("Connected" + "\nServer Name:\n\t" + inputParsed[1] +
                                   "\nSupported Features:" + features);
                break;
            case "LOGIN":
                System.out.println("Logged In");
                break;
            case "ALREADYLOGGEDIN":
                System.out.println(
                        "This username already exists! Please use the [setname] command to set a " +
                        "new name");
                client.setValidName(false);
                break;
            case "MOVE":
                client.getGame().listenerSetBoard(
                        Integer.parseInt(inputParsed[1]),
                        Integer.parseInt(inputParsed[2]));
                if (client.getPlayer() instanceof Bot && client.getMoveCounter() % 2 == 0 &&
                    !client.getGame().isGameOver()) {
                    client.makePlayerDoMove();
                }
                client.setMoveCounter(client.getMoveCounter() + 1);
                System.out.println(client.getGame().update());
                System.out.println(client.getMoveCounter() % 2 == 1 ? "It's now your turn" :
                                   "It's now the other player's turn");
                break;
            case "PING":
                network.sendMessage("PONG");
                break;
            case "PONG":
                System.out.println("Server up!");
                break;
            case "CHALLENGE":
                // TODO : Implement Auth
                break;
            case "LIST":
                String allUsers = "";
                for (int i = 1; i < inputParsed.length; i++) {
                    allUsers = allUsers + "\n\t- " + inputParsed[i];
                }
                System.out.println("Connected:" + allUsers);
                break;
            case "NEWGAME":
                System.out.println(
                        "New Game:" + "\n\tPlayer 1: " + inputParsed[1] + "\n\tPlayer 2: " +
                        inputParsed[2]);
                client.startNewGame(inputParsed[1], inputParsed[2]);
                boolean areWeStarting = client.getPlayer().getName().equals(inputParsed[1]);
                System.out.println(
                        areWeStarting ? "It's our turn" : "It's the other player's turn");
                if (areWeStarting) {
                    if (client.getPlayer() instanceof Bot) {
                        client.makePlayerDoMove();
                    }
                    client.setMoveCounter(client.getMoveCounter() + 1);
                }
                break;
            case "GAMEOVER":
                switch (inputParsed[1]) {
                    case "VICTORY":
                        if (client.getPlayer().getName().equals(inputParsed[2])) {
                            System.out.println("We won!!");
                        } else {
                            System.out.println("We lost...");
                        }
                        break;
                    case "DISCONNECT":
                        System.out.println(inputParsed[2] + " Won the game by disconnect!");
                        break;
                    case "DRAW":
                        System.out.println("The game ended in a draw!");
                        break;
                    default:
                        System.out.println("ERR: unexpected win condition");
                        break;
                }
                client.setMoveCounter(0);
                client.endCurrentGame();
                if (client.isAutoQueue()) {
                    System.out.println("Queueing again...");
                    network.sendMessage("QUEUE");
                }
                break;
            case "CHAT":
                System.out.println(
                        "CHAT" + "\n\tFROM: " + inputParsed[1] + "\n\tMESSAGE: " + inputParsed[2]);
                break;
            case "WHISPER":
                System.out.println("WHISPER" + "\n\tFROM: " + inputParsed[1] + "\n\tMESSAGE: " +
                                   inputParsed[2]);
                break;
            case "CANNOTWHISPER":
                System.out.println("ERR:\n\tCannot whisper to user");
                break;
            case "ERROR":
                System.out.println("ERR:\n\t" + inputParsed[1]);
                break;
            default:
                System.out.println("ERR:\n\tUnexpected message from server: " + inputParsed[0]);
                break;
        }
    }

    /**
     * Reads from the socket until it closes.
     */
    @Override
    public void run() {
        if (this.socket.isClosed()) {
            return;
        }
        try {
            String output;
            while ((output = br.readLine()) != null) {
                messageParser(output);
            }
        } catch (IOException e) {
            close();
        }
    }
}
