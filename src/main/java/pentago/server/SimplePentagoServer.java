package pentago.server;

import java.io.IOException;
import java.net.ServerSocket;
import java.util.*;

public class SimplePentagoServer implements PentagoServer{
    private ServerSocket serverSocket;
    private List<ClientHandler> clients;
    private Queue<ClientHandler> queue;

    @Override
    public void start(int port) {
        try {
            serverSocket = new ServerSocket(port);
            System.out.println("Server: " + serverSocket.getLocalSocketAddress());
            clients = new ArrayList<>();
            queue = new ArrayDeque<>();

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
            if (queue.contains(clientHandler)) {
                queue.remove(clientHandler);
            }

            if (clients.contains(clientHandler)) {
                clients.remove(clientHandler);
                return;
            }
            System.out.println("ERR:\n\tAttempted to remove client, but it did not exist");
        }
    }

    public List<String> getAllUsernames() {
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

    public ClientHandler getNextInQueue() {
        synchronized (queue) {
            return queue.remove();
        }
    }

    public void startNewGame() {
        Random random = new Random();
        Game game;
        ClientHandler player1;
        ClientHandler player2;

        synchronized (queue) {
            if (queue.size() <= 1) {
                return;
            }
            player1 = getNextInQueue();
            player2 = getNextInQueue();
        }

        String message;
        if (random.nextInt(2) == 0) {
            game = new Game(player1, player2);
            message = "NEWGAME~" + player1.getUsername() + "~" + player2.getUsername();
        } else {
            game = new Game(player2, player1);
            message = "NEWGAME~" + player2.getUsername() + "~" + player1.getUsername();
        }
        player1.setGame(game);
        player2.setGame(game);
        player1.sendMessage(message);
        player2.sendMessage(message);
    }

    public void sendChat(ClientHandler sender, String message) {
        synchronized (clients) {
            for (ClientHandler client : clients) {
                if (client == sender) {
                    continue;
                }
                client.sendMessage("CHAT~" + sender.getUsername() + "~" + message);
            }
        }
    }

    public void sendWhisper(ClientHandler sender, String receiver, String message) {
        if (sender.getUsername().equals(receiver)) {
            return;
        }

        synchronized (clients) {
            for (ClientHandler client : clients) {
                if (!client.getUsername().equals(receiver)) {
                    continue;
                }
                client.sendMessage("WHISPER~" + sender.getUsername() + "~" + message);
            }
        }
    }

    public boolean isUsernameInUse(String name, ClientHandler request) {
        for (ClientHandler client : clients) {
            if (client == request) {
                continue;
            }

            if (client.getUsername().equals(name)){
                return true;
            }
        }
        return false;
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
