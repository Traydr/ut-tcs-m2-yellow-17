package pentago.client;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.Socket;

public class Listener implements Runnable {
    Socket socket = null;
    BufferedReader br = null;

    Listener(Socket sock) {
        this.socket = sock;
        try {
            this.br = new BufferedReader(new InputStreamReader(this.socket.getInputStream()));
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    void close() {
        try {
            br.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    @Override
    public void run() {
        // TODO : Make this parse all commands, not just output them
        if (this.socket.isClosed()) {
            return;
        }
        try {
            String output;
            while ((output = br.readLine()) != null) {
                String[] outputParsed = output.split("~");
                System.out.println(output);
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
