package pentago.server;

import java.io.IOException;
import java.net.BindException;
import java.net.ServerSocket;
import java.util.*;

public class SimplePentagoServer implements PentagoServer {
    private ServerSocket serverSocket;
    private List<ClientHandler> clients;
    private Queue<ClientHandler> queue;
    private List<Game> activeGames;
    private String serverName;
    private ArrayList<String> supportedFeatures;
    private int gameCounter;

    /**
     * Starts the server.
     *
     * @param port port on which the server should listen on
     */
    //@ requires port >= 0 && port <= 65535;
    //@ requires name != null;
    @Override
    public void start(int port, String name) throws BindException {
        try {
            serverSocket = new ServerSocket(port);
            System.out.println("Server: " + serverSocket.getLocalSocketAddress());
            clients = new ArrayList<>();
            queue = new ArrayDeque<>();
            activeGames = new ArrayList<>();
            serverName = name;
            supportedFeatures = new ArrayList<>();
            supportedFeatures.add("CHAT");
            gameCounter = 0;

            Thread accept = new Thread(new AcceptConnection(serverSocket, this));
            accept.start();
        } catch (BindException e) {
            throw new BindException();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * Returns server name.
     *
     * @return server name
     */
    //@ requires this.serverName != null;
    //@ ensures \result == this.serverName;
    public String getServerName() {
        return serverName;
    }

    /**
     * Returns a list of the features supported by the server.
     *
     * @return list of features
     */
    //@ requires supportedFeatures != null;
    //@ ensures \result == this.supportedFeatures;
    public ArrayList<String> getSupportedFeatures() {
        return supportedFeatures;
    }

    /**
     * Adds a new client to the list of connected clients.
     *
     * @param clientHandler the client to add
     */
    //@ requires clientHandler != null && clients != null;
    //@ ensures clients.contains(clientHandler);
    public void addClient(ClientHandler clientHandler) {
        synchronized (clients) {
            clients.add(clientHandler);
        }
    }

    /**
     * Removes a specific game from the active games list.
     *
     * @param game Game object
     */
    //@ requires game != null && activeGames != null;
    //@ ensures activeGames.contains(game);
    public void removeGame(Game game) {
        if (activeGames.contains(game)) {
            activeGames.remove(game);
        }
    }

    /**
     * Removes a specific client from the list of connected clients.
     *
     * @param clientHandler the client to remove
     */
    //@ requires clients != null && clientHandler != null;
    //@ ensures !\old(clients).contains(clientHandler) ==> clients.contains(clientHandler);
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

    /**
     * Returns a list of all connected clients usernames.
     *
     * @return a list of strings containing usernames
     */
    //TODO add more conditions
    //@ requires clients != null;
    public List<String> getAllUsernames() {
        synchronized (clients) {
            ArrayList<String> output = new ArrayList<>();

            for (ClientHandler client : clients) {
                output.add(client.getUsername());
            }
            return output;
        }
    }

    /**
     * Adds a client to the queue waiting for a new game to start.
     *
     * @param clientHandler the client to add
     */
    //@ requires clientHandler != null && queue != null;
    public void addToQueue(ClientHandler clientHandler) {
        synchronized (queue) {
            if (queue.contains(clientHandler)) {
                return;
            }
            queue.add(clientHandler);
        }
    }

    /**
     * Returns the first client in queue.
     *
     * @return client in queue pos 1
     */
    //@ requires queue != null;
    public ClientHandler getNextInQueue() {
        synchronized (queue) {
            if (queue.isEmpty()) {
                return null;
            }
            return queue.remove();
        }
    }

    /**
     * Starts a new game and randomly assigns which player should go first. It then sends the new
     * game info to the clients.
     */
    //@ requires queue != null;
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

        synchronized (player1) {
            synchronized (player2) {
                if (player1.isAlreadyInGame() && player2.isAlreadyInGame()) {
                    return;
                } else if (player1.isAlreadyInGame()) {
                    addToQueue(player2);
                    return;
                } else if (player2.isAlreadyInGame()) {
                    addToQueue(player1);
                    return;
                }

                String message;
                if (random.nextInt(2) == 0) {
                    game = new Game(player1, player2);
                    message = "NEWGAME~" + player1.getUsername() + "~" + player2.getUsername();
                } else {
                    game = new Game(player2, player1);
                    message = "NEWGAME~" + player2.getUsername() + "~" + player1.getUsername();
                }
                activeGames.add(game);
                player1.setGame(game);
                player2.setGame(game);
                player1.sendMessage(message);
                player2.sendMessage(message);
                player1.setHasSentNewGame(true);
                player2.setHasSentNewGame(true);

                gameCounter += 1;
                System.out.println(gameCounter);
            }
        }
    }

    /**
     * Sends a chat to all connected clients that support the CHAT feature.
     *
     * @param sender  The client that is sending the message
     * @param message The message itself
     */
    public void sendChat(ClientHandler sender, String message) {
        synchronized (clients) {
            for (ClientHandler client : clients) {
                // TODO Transfer this clientSupportedFeatures check to ClientHandler
                if (client == sender && !client.clientSupportedFeatures.contains("CHAT")) {
                    continue;
                }
                client.sendMessage("CHAT~" + sender.getUsername() + "~" + message);
            }
        }
    }

    /**
     * Sends a whisper to a specific client.
     *
     * @param sender   the client sending the message
     * @param receiver the client receiving the message
     * @param message  the message to be sent
     */
    public void sendWhisper(ClientHandler sender, String receiver, String message) {
        if (sender.getUsername().equals(receiver)) {
            return;
        }

        synchronized (clients) {
            for (ClientHandler client : clients) {
                if (!client.getUsername().equals(receiver) &&
                    !client.clientSupportedFeatures.contains("CHAT")) {
                    continue;
                }
                client.sendMessage("WHISPER~" + sender.getUsername() + "~" + message);
            }
        }
    }

    /**
     * Checks whether a certain username is already being used by another client.
     *
     * @param name    The name of the client
     * @param request The client itself
     * @return true if the username is already in user, otherwise false
     */
    public boolean isUsernameInUse(String name, ClientHandler request) {
        synchronized (clients) {
            for (ClientHandler client : clients) {
                if (client == request) {
                    continue;
                }

                if (client.getUsername().equals(name)) {
                    return true;
                }
            }
            return false;
        }
    }

    /**
     * Returns the port of the server.
     *
     * @return port
     */
    @Override
    public int getPort() {
        return serverSocket.getLocalPort();
    }

    /**
     * Stops the server by closing the socket.
     */
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
