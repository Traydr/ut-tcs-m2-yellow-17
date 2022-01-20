package pentago.client;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
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
                    features = inputParsed[i] + ", ";
                }
                System.out.println("Success : Hello\nServer Name : " + inputParsed[1] +
                                   "\nSupported Features : ");
                break;
            case "LOGIN":
                System.out.println("Success : Login");
                break;
            case "MOVE":
                // TODO : Implement game functions & Ignore when server repeats moves
                System.out.println("Server moved: " + inputParsed[1] + " " + inputParsed[2]);
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
                    allUsers = inputParsed + ", ";
                }
                System.out.println("Currently connected: " + allUsers);
            case "NEWGAME":
                System.out.println("Player 1: " + inputParsed[1] + "Player 2: " + inputParsed[2]);
                break;
            case "GAMEOVER":
                System.out.println("Gameover");
                break;
            case "CHAT":
                System.out.println("FROM: " + inputParsed[1] + " | MESSAGE: " + inputParsed[2]);
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
                messageParser(output);
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
