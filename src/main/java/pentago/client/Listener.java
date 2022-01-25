package pentago.client;

import pentago.client.player.Bot;
import pentago.client.player.Player;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.Socket;

public class Listener implements Runnable {
    Socket socket = null;
    BufferedReader br = null;
    Network network = null;
    PentagoClient client = null;

    Listener(Socket sock, Network net, PentagoClient client) {
        this.socket = sock;
        this.network = net;
        this.client = client;
        try {
            this.br = new BufferedReader(new InputStreamReader(this.socket.getInputStream()));
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    void close() {
        try {
            br.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public void messageParser(String input) {
        String[] inputParsed = input.split("~");

        switch (inputParsed[0]) {
            case "HELLO":
                String features = "";
                for (int i = 2; i < inputParsed.length; i++) {
                    features = features + "\n- " + inputParsed[i];
                }
                System.out.println("Connected" + "\nServer Name:\n- " + inputParsed[1] +
                                   "\nSupported Features:" + features);
                break;
            case "LOGIN":
                System.out.println("Logged In");
                break;
            case "ALREADYLOGGEDIN":
                System.out.println("ERR: already logged in");
                break;
            case "MOVE":
                client.game.listenerSetBoard(Integer.parseInt(inputParsed[1]),
                                             Integer.parseInt(inputParsed[2]));
                System.out.println(
                        "\nServer" + " pos:" + inputParsed[1] + " rotate:" + inputParsed[2]);
                client.player.isOurTurn = !client.player.isOurTurn;
                if (client.player instanceof Bot && client.player.isOurTurn) {
                    client.makePlayerDoMove();
                }
                System.out.println(client.game.update());
                break;
            case "PING":
                network.sendMessage("PONG");
                break;
            case "PONG":
                System.out.println("\nServer up!");
                break;
            case "CHALLENGE":
                // TODO : Implement Auth
                break;
            case "LIST":
                String allUsers = "";
                for (int i = 1; i < inputParsed.length; i++) {
                    allUsers = allUsers + "\n\t- " + inputParsed[i];
                }
                System.out.println("\nConnected:" + allUsers);
                break;
            case "NEWGAME":
                System.out.println(
                        "\nNew Game:" + "\n\tPlayer 1: " + inputParsed[1] + "\n\tPlayer 2: " +
                        inputParsed[2]);
                client.startNewGame(inputParsed[1], inputParsed[2]);
                boolean areWeStarting = client.username.equals(inputParsed[1]);
                System.out.println(areWeStarting ? "It's our turn" : "It's the other player's turn");
                if (areWeStarting && client.player instanceof Bot) {
                    client.makePlayerDoMove();
                }
                break;
            case "GAMEOVER":
                switch (inputParsed[1]) {
                    case "VICTORY":
                        System.out.println(inputParsed[2] + " Won the game!");
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
                client.endCurrentGame();
                break;
            case "CHAT":
                //                System.out.println("\nCHAT" +
                //                                   "\n\tFROM: " + inputParsed[1] +
                //                                   "\n\tMESSAGE: " + inputParsed[2]);
                break;
            case "WHISPER":
                System.out.println("\nWHISPER" + "\n\tFROM: " + inputParsed[1] + "\n\tMESSAGE: " +
                                   inputParsed[2]);
                break;
            case "CANNOTWHISPER":
                System.out.println("\nERR:\n\tCannot whisper to user");
                break;
            case "ERROR":
                System.out.println("\nERR:\n\t" + inputParsed[1]);
                break;
        }
    }

    @Override
    public void run() {
        // TODO : Make this parse all commands, not just output them
        if (this.socket.isClosed()) {
            return;
        }
        try {
            String output;
            while ((output = br.readLine()) != null) {
                System.out.println("[SERVER]" + output);
                messageParser(output);
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
