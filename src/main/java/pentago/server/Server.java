package pentago.server;

import java.util.Scanner;

public class Server {
    /**
     * Starts a new server object and listens for a port and quit, for when to stop the server.
     * @param args
     */
    public static void main(String[] args) {
        SimplePentagoServer server = new SimplePentagoServer();
        try (Scanner scanner = new Scanner(System.in)) {
            System.out.println("What port should the server listen on (0 for random)?");
            int port = Integer.parseInt(scanner.nextLine());
            System.out.println("What should the server name be?");
            String name = scanner.nextLine();

            server.start(port, name);

            String isClosing = "";
            while (!isClosing.equals("quit")) {
                isClosing = scanner.nextLine();
            }
        }
        server.stop();
    }
}
