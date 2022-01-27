package pentago.server;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.Scanner;

public class ClientHandler implements Runnable{
    private Socket socket;
    private SimplePentagoServer server;
    private String username;
    private BufferedWriter writer;

    public ClientHandler(Socket socket, SimplePentagoServer server) throws IOException {
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
            server.removeClient(this);
        }
    }

    public void parseClient(String input) {
        String[] parsedInput = input.split("~");

        switch (parsedInput[0]) {

        }
    }

    @Override
    public void run() {
        server.addClient(this);
        try (Scanner scanner = new Scanner(new InputStreamReader(this.socket.getInputStream()))){
            // Read HELLO and LOGIN

            String input;
            while (scanner.hasNextLine()) {
                input = scanner.nextLine();
                // TODO parse input
            }
        } catch (IOException e) {
            e.printStackTrace();
        } finally {
            close();
        }

    }
}
