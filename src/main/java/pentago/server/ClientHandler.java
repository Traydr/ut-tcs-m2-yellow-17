package pentago.server;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.net.Socket;

public class ClientHandler implements Runnable{
    private Socket socket;
    private PentagoServer server;
    private String username;
    private BufferedWriter writer;

    public ClientHandler(Socket socket, PentagoServer server) throws IOException {
        this.socket = socket;
        this.server = server;
        this.writer = new BufferedWriter(new OutputStreamWriter(this.socket.getOutputStream()));
    }

    public String getUsername() {
        return username;
    }

    public void sendMessage(String message) {
        try {
            this.writer.write(message + "\n");
            this.writer.flush();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public void close() {
        try {
            if (!socket.isClosed()) {
                socket.close();
            }
        } catch (IOException e) {
            e.printStackTrace();
        } finally {
            //TODO Uncomment this when it is implemented
            //server.removeClient(this)
        }
    }

    @Override
    public void run() {

    }
}
