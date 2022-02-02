package pentago.server;

import java.net.BindException;
import java.util.Scanner;

public class Server {
    /**
     * Starts a new server object and listens for a port and quit, for when to stop the server.
     *
     * @param args
     */
    public static void main(String[] args) {
        SimplePentagoServer server = new SimplePentagoServer();
        try (Scanner scanner = new Scanner(System.in)) {
            boolean validPort = false;
            System.out.println("What should the server name be?");
            String name = scanner.nextLine();

            while (!validPort) {
                try {
                    System.out.println("What port should the server listen on (0 for random)?");
                    int port = Integer.parseInt(scanner.nextLine());
                    server.start(port, name);
                    validPort = true;
                } catch (BindException e) {
                    System.out.println("Couldn't bind to this port, please enter another one");
                }
            }
            String isClosing = "";
            while (!isClosing.equals("quit")) {
                isClosing = scanner.nextLine();
            }
            server.stop();
        }
    }
}
