package pentago.game_logic;

public class CommandParser {

    /**
     * Changes the local coordinate representation to the protocol coordinate representation.
     *
     * @param quadrant The quadrant of the coordinate
     * @param x        The horizontal position of the coordinate
     * @param y        The vertical position of the coordinate
     * @return Coordinate from 0 to 35
     */
    //@ requires quadrant >= 0 || quadrant <= 3;
    //@ requires x >= 0 || x <= 3;
    //@ requires y >= 0 || y <= 3;
    //@ ensures \result >= 0 || \result <= 35;
    public static int localToProtocolCoords(int quadrant, int x, int y) {
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

        return x + y * 6 + offset; // Calculate the index used in the protocol
    }

    /**
     * Changes the protocol coordinate representation to the local coordinate representation.
     *
     * @param serverCoords Number from 0 to 35
     * @return an array of size 3 {quad, x, y}
     */
    //@ requires serverCoords >= 0 || serverCoords <= 35;
    public static int[] protocolToLocalCoords(int serverCoords) {
        int[] gameCoords = new int[3];
        int tmpNum = serverCoords;

        // Divide num by 3, round down
        // If even then it is on the left quads, else right quads
        // if num is >= 18 then it is on the 2nd row

        // Figure out the quad
        tmpNum = tmpNum / 3;

        if (tmpNum % 2 == 0) {
            gameCoords[0] = 0;
        } else {
            gameCoords[0] = 1;
        }

        if (serverCoords >= 18) {
            gameCoords[0] += 2;
        }

        // x coord
        gameCoords[1] = serverCoords % 3;

        // y coord
        gameCoords[2] = serverCoords / 6 % 3;
        return gameCoords;
    }

    /**
     * Changes the local rotate representation to the protocol rotate representation.
     *
     * @param cmd [A-D][L|R]
     * @return number from 0 to 7
     */
    //@ requires cmd != null;
    //@ ensures \result >= 0 || \result <= 8;
    public static int localToProtocolRotate(String cmd) {
        int quad = (int) cmd.charAt(0) - 65;
        if (cmd.charAt(1) == 'L') {
            return quad * 2;
        }
        return quad * 2 + 1;
    }

    /**
     * Changes the protocol rotate representation to the local rotate representation.
     *
     * @param serverRotate Protocol number 0 to 7
     * @return [A-D][L|R]
     */
    //@ requires serverRotate >= 0 || serverRotate <= 8;
    //@ ensures \result != null;
    public static String protocolToLocalRotate(int serverRotate) {
        String output;
        int serRot = serverRotate;
        int quadChar;

        if (serverRotate % 2 == 0) {
            output = "L";
            quadChar = (serverRotate / 2) + 65;
        } else {
            output = "R";
            serRot -= 1;
            quadChar = (serRot / 2) + 65;
        }
        output = ((char) quadChar) + output;

        return output;
    }
}
