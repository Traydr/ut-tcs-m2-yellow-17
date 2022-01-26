package pentago.client;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;

public class Networking implements Network {
    Socket socket = null;
    BufferedWriter bw;
    Listener listener;

    @Override
    public boolean connect(InetAddress address, int port, PentagoClient client) {
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
            if (!this.socket.isClosed()) {
                this.socket.close();
            }
            this.bw.close();
            this.listener.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    @Override
    public boolean sendMessage(String message) {
        // TODO : Change so more commands are accepted
        try {
//            System.out.println("[SENDING]" + message);
            bw.write(message + "\n");
            bw.flush();
            return true;
        } catch (IOException e) {
            e.printStackTrace();
            close();
            return false;
        }
    }
}
