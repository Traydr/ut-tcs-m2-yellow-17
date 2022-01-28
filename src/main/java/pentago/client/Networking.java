package pentago.client;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.Scanner;

public class Networking implements Network {
    Socket socket = null;
    BufferedWriter bw;
    Listener listener;
    PentagoClient client;

    @Override
    public boolean connect(InetAddress address, int port, PentagoClient pentagoClient) {
        this.client = pentagoClient;
        try {
            this.socket = new Socket(address, port);
            this.bw = new BufferedWriter(new OutputStreamWriter(this.socket.getOutputStream()));
            listener = new Listener(this.socket, this, client);
            Thread thread = new Thread(listener);
            thread.start();
            return true;
        } catch (IOException e) {
            return false;
        }
    }

    @Override
    public void close() {
        try {
            this.bw.close();
            this.listener.close();
            if (!this.socket.isClosed()) {
                this.socket.close();
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    @Override
    public boolean sendMessage(String message) {
        try {
            // <-------- DEBUG -------->
            //System.out.println("[SENDING]" + message);
            // <-------- DEBUG -------->
            bw.write(message + "\n");
            bw.flush();
            return true;
        } catch (IOException e) {
            System.out.println("It looks like the pipe to the server is closed...");
            System.out.println("Do you want to reconnect? Y/n");
            Scanner scanner = new Scanner(System.in);
            String input = scanner.nextLine();
            if (input.equals("n")) {
                close();
                scanner.close();
                return false;
            } else {
                System.out.println("Reconnecting...");
                try {
                    if (!client.network.connect(
                            InetAddress.getByName(client.serverAddress), client.port, client)) {
                        System.out.println("ERR: bad connection");
                        System.exit(1);
                    }
                } catch (UnknownHostException exception) {
                    System.out.println("ERR: no connection");
                    System.exit(2);
                }

                client.connectToServer();
                return true;
            }
        }
    }
}
