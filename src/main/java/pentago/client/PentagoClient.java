package pentago.client;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Scanner;

public class PentagoClient {
    public String serverAddress;
    public int port;
    public String username;
    public Network network;
    public Game game;

    public PentagoClient(String serverAddress, int port, String username) {
        this.serverAddress = serverAddress;
        this.port = port;
        this.username = username;
        this.network = new Networking();
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

        connectToServer(client.network, client.username);

        String output;
        while (scanner.hasNextLine()) {
            output = scanner.nextLine();
            if (output.equals("quit")) {
                break;
            } else if (output.contains("~")) {
                System.out.println("\nInput cannot contain \"~\" characters");
                continue;
            } else {
                parseInput(client.network, output);
            }
        }

        scanner.close();
    }

    public static void connectToServer(Network net, String username) {
        net.sendMessage("HELLO~" + username + "~CHAT");
        net.sendMessage("LOGIN~" + username);
    }

    public static void parseInput(Network net, String input) {
        String[] parsedInput = input.split(" ");
        switch (input) {
            case "help":
                break;
            case "move":
                break;
            case "rotate":
                break;
            case "ping":
                break;
            default:
                System.out.println("Unknown Command: " + parsedInput[0]);
                break;
        }
    }

    public static void displayHelp() {
        // TODO : Make these simpler for the user
        System.out.println("Commands: \n" + "HELLO~<client description>[~extension]*\n" +
                           "LOGIN~<username>\n" + "LIST\n" + "QUEUE\n" + "MOVE~<A>~<B>\n" +
                           "PING\n" + "PONG\n" + "QUIT\n");
    }
}
