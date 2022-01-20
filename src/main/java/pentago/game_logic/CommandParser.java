package pentago.game_logic;

public class CommandParser {
    public static int clientToServer(int quadrant, int x, int y) {
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
}
