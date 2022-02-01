package pentago.client;

import java.net.InetAddress;

public interface Network {
    /**
     * Attempts connection to the server.
     *
     * @param address address of the server
     * @param port    port of the server
     * @return true on success, false on failure
     */
    boolean connect(InetAddress address, int port, PentagoClient client);

    /**
     * Closes the network connection.
     */
    void close();

    /**
     * Sends a message to the server.
     *
     * @param message message to be sent
     * @return true on success, false on failure
     */
    boolean sendMessage(String message);
}
