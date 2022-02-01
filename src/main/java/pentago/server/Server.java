package pentago.server;

import java.util.Scanner;

public class Server {
    public static void main(String[] args) {
        SimplePentagoServer server = new SimplePentagoServer();
        try (Scanner scanner = new Scanner(System.in)) {
            System.out.println("What port should the server listen on (0 for random)?");
            int port = Integer.parseInt(scanner.nextLine());
            server.start(port);
            System.out.println(server.getPort());

            // TODO Don't think this works perfectly
            String isClosing = "";
            while (!isClosing.equals("quit")) {
                isClosing = scanner.nextLine();
            }
        }

        server.stop();
    }
}
