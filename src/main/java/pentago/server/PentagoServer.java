package pentago.server;

import java.net.BindException;

public interface PentagoServer {
    /**
     * Starts the server, using the port provided in the constructor.
     */
    void start(int port) throws BindException;

    /**
     * Returns the port of the server.
     * @return port.
     */
    int getPort();

    /**
     * Stops the server.
     */
    void stop();
}
