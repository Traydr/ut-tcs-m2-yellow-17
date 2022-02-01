package pentago.server;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;

public class AcceptConnection implements Runnable {
    ServerSocket serverSocket;
    SimplePentagoServer gameServer;

    public AcceptConnection(ServerSocket serverSocket, SimplePentagoServer gameServer) {
        this.serverSocket = serverSocket;
        this.gameServer = gameServer;
    }

    @Override
    public void run() {
        Socket client = null;
        while (!serverSocket.isClosed()) {
            try {
                client = serverSocket.accept();
            } catch (IOException e) {
                System.out.println("The socket is closed");
            }

            if (client != null) {
                ClientHandler clientHandler = null;
                try {
                    clientHandler = new ClientHandler(client, gameServer);
                } catch (IOException e) {
                    System.out.println("The socket is closed");
                }
                Thread chatClient = new Thread(clientHandler);
                chatClient.start();
            }
        }
    }
}
