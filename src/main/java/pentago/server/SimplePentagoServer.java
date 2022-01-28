package pentago.server;

import java.io.IOException;
import java.net.ServerSocket;
import java.util.ArrayList;
import java.util.List;
import java.util.Queue;

public class SimplePentagoServer implements PentagoServer{
    private ServerSocket serverSocket;
    private List<ClientHandler> clients = new ArrayList<>();
    private Queue<ClientHandler> queue;

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

    public ArrayList<String> allClientUsernames() {
        ArrayList<String> output = new ArrayList<>();

        for (ClientHandler client : clients) {
            output.add(client.getUsername());
        }
        return output;
    }

    public void addToQueue(ClientHandler clientHandler) {
        synchronized (queue) {
            queue.add(clientHandler);
        }
    }

    public ClientHandler removeFromQueue() {
        synchronized (queue) {
            return queue.remove();
        }
    }

    public int getQueueLength() {
        return queue.size();
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
