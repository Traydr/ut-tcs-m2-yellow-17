package pentago.client;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;

public class Networking implements Network{
    Socket socket = null;
    BufferedWriter bw;
    BufferedReader br;

    @Override
    public boolean connect(InetAddress address, int port) {
        try {
            this.socket = new Socket(address, port);
            this.bw = new BufferedWriter(new OutputStreamWriter(this.socket.getOutputStream()));
            this.br = new BufferedReader(new InputStreamReader(this.socket.getInputStream()));
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
            this.br.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    @Override
    public boolean sendMessage(String message) {
        // TODO : Change so more commands are accepted
        try {
            bw.write("SAY~" + message + "\n");
            bw.flush();
            return true;
        } catch (IOException e) {
            e.printStackTrace();
            close();
            return false;
        }
    }

    @Override
    public void addChatListener() {
    }

    @Override
    public void removeChatListener() {
    }
}
