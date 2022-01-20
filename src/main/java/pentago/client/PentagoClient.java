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
            output = scanner.nextLine();
            if (output.equals("quit")) {
                break;
            }
            else if (output.equals("")) {
                continue;
            }
            System.out.println("o: " + output);

            network.sendMessage(output);
        }

        scanner.close();
    }
}
