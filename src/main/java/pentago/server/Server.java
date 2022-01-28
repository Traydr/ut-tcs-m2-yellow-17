package pentago.server;

import java.util.Scanner;

public class Server {
    public static void main(String[] args) {
        SimplePentagoServer server = new SimplePentagoServer();
        server.start();
        System.out.println(server.getPort());

        String isClosing = "";
        while (!isClosing.equals("quit")) {
            try (Scanner scanner = new Scanner(System.in)) {
                isClosing = scanner.nextLine();
            }
        }

        server.stop();
    }
}
