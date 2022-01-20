package pentago.client;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Scanner;

public class PentagoClient {
    // Reference server 130.89.253.64 55555

    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        String serverAddress;
        int port;
        String username;
        Network network = new Networking();

        System.out.println("Server Addr:");
        //serverAddress = scanner.nextLine();
        System.out.println("Server Port:");
        //port = scanner.nextInt();

        System.out.println("Username:");
        username = scanner.nextLine();

        // DEBUG SO I DONT HAVE TO KEEP TYPING
        serverAddress = "130.89.253.64";
        port = 55555;

        try {
            if (!network.connect(InetAddress.getByName(serverAddress), port)) {
                System.out.println("ERR: BAD CONNECTION");
            }
        } catch (UnknownHostException e) {
            e.printStackTrace();
        }

        //TODO : Make connection better
        network.sendMessage("HELLO~" + username);
        network.sendMessage("LOGIN~" + username);

        String output;
        while (scanner.hasNextLine()) {
            // TODO : Add exception for ~ chars so that user can't us them
            output = scanner.nextLine();
            if (output.equals("quit")) {
                break;
            }
            else if (output.equals("")) {
                continue;
            }
            else if (output.equals("help")) {
                displayHelp();
                continue;
            }

            network.sendMessage(output);
        }

        scanner.close();
    }

    public static void displayHelp() {
        // TODO : Make these simpler for the user
        System.out.println("Commands: \n" +
                "HELLO~<client description>[~extension]*\n" +
                "LOGIN~<username>\n" +
                "LIST\n" +
                "QUEUE\n" +
                "MOVE~<A>~<B>\n" +
                "PING\n" +
                "PONG\n" +
                "QUIT\n");
    }
}
