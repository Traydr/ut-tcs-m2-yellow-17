package pentago.game_logic;

import java.util.Arrays;

public class Board {
    public final int QUADRANT_SIZE = 3;
    public final int QUADRANT_NUM = 4;
    private final int CHARACTER_OFFSET = 65;

    private Mark[][][] quadrants;
    private boolean isTurnFirstPlayer;

    /**
     * This creates an empty board and set it that its the first players turn
     */
    public Board() {
        this.quadrants = new Mark[QUADRANT_NUM][QUADRANT_SIZE][QUADRANT_SIZE];
        this.isTurnFirstPlayer = true;
        this.reset(); // Initialize the board by filling it in with empty marks
    }

    /**
     * This sets all the positions of the board to be empty
     */
    public void reset() {
        Arrays.fill(this.quadrants[0][0], Mark.EMPTY);
        Arrays.fill(this.quadrants[0], this.quadrants[0][0]);
        Arrays.fill(this.quadrants, this.quadrants[0]);
    }

    /**
     * Used to turn a combination of letters A-D and 0-8 to an array of 3 indexes
     *
     * @param userCoords A combination a letters A-D and 0-8
     * @return An array of 3 indexes indicating quadrants and x, y within them
     */
    public int[] getCoords(String userCoords) {
        if (userCoords.length() != 2) {
            return null;
        }

        int[] qxy = new int[3];
        char quad = userCoords.charAt(0);
        int index = Integer.parseInt(String.valueOf(userCoords.charAt(1)));

        qxy[0] = (int) quad - CHARACTER_OFFSET; // Convert letters to the numeric position in the alphabet to get the quadrant
        qxy[1] = index % QUADRANT_SIZE; // Java rounds down integers, so this gives us the x coordinate
        qxy[2] = index / QUADRANT_SIZE; // This gives us the y coordinate

        return qxy;
    }

    public boolean isField(int quad, int x, int y) {
        return (quad >= 0 && quad <= QUADRANT_NUM && x >= 0 && x <= QUADRANT_SIZE && y >= 0 && y <= QUADRANT_SIZE);
    }

    public boolean isField(String userCoords) {
        int[] coords = getCoords(userCoords);
        return isField(coords[0], coords[1], coords[2]);
    }

    public Mark getField(int quad, int x, int y) {
        return this.quadrants[quad][x][y];
    }

    public Mark getField(String userCoords) {
        int[] coords = getCoords(userCoords);
        return getField(coords[0], coords[1], coords[2]);
    }

    public boolean isEmptyField(int quad, int x, int y) {
        return (getField(quad, x, y) == Mark.EMPTY);
    }

    public boolean isEmptyField(String userCoords) {
        int[] coords = getCoords(userCoords);
        return isField(coords[0], coords[1], coords[2]);
    }

    public boolean isFull() {
        for (int i = 0; i < QUADRANT_NUM; i++) {
            for (int j = 0; j < QUADRANT_SIZE; j++) {
                for (int k = 0; k < QUADRANT_SIZE; k++) {
                    if (isEmptyField(i, j, k)) {
                        return false;
                    }
                }
            }
        }

        return true;
    }

    public boolean hasRow(Mark mark) {
        return false;
    }

    public boolean hasColumn(Mark mark) {
        return false;
    }

    public boolean hasDiagonal(Mark mark) {
        return false;
    }

    public boolean isWinner(Mark mark) {
        return hasRow(mark) || hasColumn(mark) || hasDiagonal(mark);
    }

    public boolean hasWinner() {
        return isWinner(Mark.BLACK) || isWinner(Mark.WHITE);
    }

    public boolean gameOver() {
        return isFull() || hasWinner();
    }

    public String toString() {
        // TODO: Actually make this work
        return "";
    }

    public void setField(int quad, int x, int y, Mark mark) {
        this.quadrants[quad][x][y] = mark;
    }

    public void setField(String userCoords, Mark mark) {
        int[] coords = getCoords(userCoords);
        setField(coords[0], coords[1], coords[2], mark);
    }
}
