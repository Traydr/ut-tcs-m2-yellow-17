package pentago.game_logic;

public class CommandParser {
    public static int clientServerCoords(int quadrant, int x, int y) {
        int offset;

        switch (quadrant) {
            case 1:
                offset = 3;
                break;
            case 2:
                offset = 18;
                break;
            case 3:
                offset = 21;
                break;
            default:
                offset = 0;
        }
        return x + y * 6 + offset;
    }

    public static String serverClientCoords(int serverCoords) {
        return "";
    }

    public static int clientServerRotate(String cmd) {
        return 0;
    }

    public static String serverClientRotate(int serverRotate) {
        return "";
    }
}
