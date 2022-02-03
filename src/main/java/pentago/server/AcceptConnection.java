package pentago.server;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;

public class AcceptConnection implements Runnable {
    ServerSocket serverSocket;
    SimplePentagoServer gameServer;
    //@ invariant gameServer != null;
    //@ invariant serverSocket != null;

    /**
     * Constructor for the AcceptConnection object.
     *
     * @param serverSocket The socket for the server
     * @param gameServer   The server object itself
     */
    //@ requires gameServer != null;
    //@ requires serverSocket != null;
    //@ ensures this.serverSocket == serverSocket;
    //@ ensures this.gameServer == gameServer;
    public AcceptConnection(ServerSocket serverSocket, SimplePentagoServer gameServer) {
        this.serverSocket = serverSocket;
        this.gameServer = gameServer;
    }

    /**
     * Waits for new connections to connect and then assigns a new client handler object to them.
     */
    @Override
    public void run() {
        Socket client = null;
        while (!serverSocket.isClosed()) {
            try {
                // Waits for a new connection to form, makes a new client object and hands it
                // off to a new client handler thread
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
