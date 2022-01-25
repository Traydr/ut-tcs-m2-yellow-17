package pentago.client;

import java.net.InetAddress;

public interface Network {
    /**
     *
     * @param address
     * @param port
     * @return true on success, false on failure
     */
    boolean connect(InetAddress address, int port, PentagoClient client);

    /**
     *
     */
    void close();

    /**
     *
     * @param message
     * @return true on success, false on failure
     */
    boolean sendMessage(String message);
}
