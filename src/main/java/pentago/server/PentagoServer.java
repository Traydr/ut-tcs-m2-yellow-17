package pentago.server;

import java.net.BindException;

public interface PentagoServer {
    /**
     * Starts the server.
     *
     * @param port the port the server should run on
     * @param name the name of the server
     * @throws BindException exception if the server couldn't connect to the port
     */
    void start(int port, String name) throws BindException;

    /**
     * Returns the port of the server.
     *
     * @return port.
     */
    int getPort();

    /**
     * Stops the server.
     */
    void stop();
}
