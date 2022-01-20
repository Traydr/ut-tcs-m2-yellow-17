package pentago.client;

import java.io.*;
import java.net.Socket;

public class Listener implements Runnable {
    Socket socket = null;
    BufferedReader br = null;
    Network network = null;

    Listener(Socket sock, Network net) {
        this.socket = sock;
        this.network = net;
        try {
            this.br = new BufferedReader(new InputStreamReader(this.socket.getInputStream()));
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    // TODO : Should replace switch statement with these
    public enum cmd {
        HELLO, LOGIN, MOVE, PING, PONG, LIST, NEWGAME, QUEUE, GAMEOVER, QUIT, ERROR, CHAT, WHISPER,
        CHALLENGE;

        @Override
        public String toString() {
            return this.name();
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
                    features = features + " | " + inputParsed[i];
                }
                System.out.println("Hello : Success" +
                           "\nServer Name : " + inputParsed[1] +
                           "\nSupported Features : " + features);
                break;
            case "LOGIN":
                System.out.println("Login : Success");
                break;
            case "MOVE":
                // TODO : Implement game functions & Ignore when server repeats moves
                System.out.println("Server" +
                           " pos:" + inputParsed[1] +
                           " rotate:" + inputParsed[2]);
                break;
            case "PING":
                // TODO : Implement this in a better way
                network.sendMessage("PONG");
                break;
            case "PONG":
                System.out.println("Server is still alive!");
                break;
            case "CHALLENGE":
                // TODO : Implement Auth
                break;
            case "LIST":
                String allUsers = "";
                for (int i = 1; i < inputParsed.length; i++) {
                    allUsers = allUsers + " | " + inputParsed[i];
                }
                System.out.println("Currently connected: " + allUsers);
                break;
            case "NEWGAME":
                System.out.println("New game started:" +
                           "\nPlayer 1: " + inputParsed[1] +
                           "\nPlayer 2: " + inputParsed[2]);
                break;
            case "GAMEOVER":
                System.out.println("GAME OVER\nWinner: " + inputParsed[1] +
                           "\nLoser: " + inputParsed[2]);
                break;
            case "CHAT":
                System.out.println("FROM: " + inputParsed[1] + " | MESSAGE: " + inputParsed[2]);
                break;
            case "WHISPER":
                System.out.println("WHISPER \nFROM: " + inputParsed[1] + " | MESSAGE: " +
                           inputParsed[2]);
                break;
            case "QUIT":
                // TODO : Implement disconnect
                break;
            case "ERROR":
                System.out.println("ERR: " + inputParsed[1]);
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
                System.out.println("[SEVER]" + output);
                messageParser(output);
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
