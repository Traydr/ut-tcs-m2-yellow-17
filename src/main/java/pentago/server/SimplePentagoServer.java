package pentago.server;

import java.io.IOException;
import java.net.ServerSocket;
import java.util.ArrayList;
import java.util.List;

public class SimplePentagoServer implements PentagoServer{
    ServerSocket serverSocket;
    List<ClientHandler> clients = new ArrayList<>();

    @Override
    public void start() {
        try {
            serverSocket = new ServerSocket(0);
            System.out.println("Server: " + serverSocket.getLocalSocketAddress());
            Thread accept = new Thread(new AcceptConnection(serverSocket, this));
            accept.start();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public void addClient(ClientHandler clientHandler) {
        synchronized (clients) {
            clients.add(clientHandler);
        }
    }

    public void removeClient(ClientHandler clientHandler) {
        synchronized (clients) {
            if (clients.contains(clientHandler)) {
                clients.remove(clientHandler);
                return;
            }
            System.out.println("ERR:\n\tAttempted to remove client, but it did not exist");
        }
    }

    @Override
    public int getPort() {
        return serverSocket.getLocalPort();
    }

    @Override
    public void stop() {
        try {
            if (!serverSocket.isClosed()) {
                serverSocket.close();
            }
        } catch (IOException e) {
            System.out.println("ERR:\n\tserver socket is already closed");
        }

    }
}
