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
        for (int i = 0; i < QUADRANT_NUM; i++) {
            for (int j = 0; j < QUADRANT_SIZE; j++) {
                for (int k = 0; k < QUADRANT_SIZE; k++) {
                    this.quadrants[i][j][k] = Mark.EMPTY;
                }
            }
        }
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

    /**
     * Check if this field exists
     * @param quad The quadrant to look at
     * @param x x position
     * @param y y position
     * @return true if field exists, false if not
     */
    public boolean isField(int quad, int x, int y) {
        return (quad >= 0 && quad <= QUADRANT_NUM - 1 && x >= 0 && x <= QUADRANT_SIZE - 1 && y >= 0 && y <= QUADRANT_SIZE - 1);
    }

    /**
     * Translates coords in format [A-D][0-8] to 3 indexes and then calls itself with coords
     * @param userCoords [A-D][0-8]
     * @return true if field exists, false if not
     */
    public boolean isField(String userCoords) {
        int[] coords = getCoords(userCoords);
        return isField(coords[0], coords[1], coords[2]);
    }

    /**
     * Returns the mark present in the field
     * @param quad The quadrant to look at
     * @param x x position
     * @param y y position
     * @return The mark in the field
     */
    public Mark getField(int quad, int x, int y) {
        return this.quadrants[quad][x][y];
    }

    /**
     * Translates coords in format [A-D][0-8] to 3 indexes and then calls itself with coords
     * @param userCoords [A-D][0-8]
     * @return The mark in the field
     */
    public Mark getField(String userCoords) {
        int[] coords = getCoords(userCoords);
        return getField(coords[0], coords[1], coords[2]);
    }

    /**
     * Checks whether the specified field is empty
     * @param quad The quadrant to look at
     * @param x x position
     * @param y y position
     * @return True if the field is empty, false if occupied
     */
    public boolean isEmptyField(int quad, int x, int y) {
        return (getField(quad, x, y) == Mark.EMPTY);
    }

    /**
     * Translates coords in format [A-D][0-8] to 3 indexes and then calls itself with coords
     * @param userCoords [A-D][0-8]
     * @return True if the field is empty, false if occupied
     */
    public boolean isEmptyField(String userCoords) {
        int[] coords = getCoords(userCoords);
        return isField(coords[0], coords[1], coords[2]);
    }

    /**
     * Check whether the board is completely full
     * @return True if full, false if at least 1 space remains empty
     */
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

    /**
     * Hardcoded rotation for left (anti-clockwise) and right (clockwise)
     * @param cmd format [A-D][L|R]
     */
    public void rotateQuadrant(String cmd) {
        // Command that comes in is in format [A-D][L|R]
        // L for rotate anti-clockwise, R for rotate clockwise
        int quad = getCoords(cmd.charAt(0) + "0")[0];
        char rotate = cmd.charAt(1);

        Mark[][] tmpShallow = this.quadrants[quad];
        Mark[][] tmpDeep = new Mark[QUADRANT_SIZE][QUADRANT_SIZE];

        switch (rotate) {
            case 'L':
                tmpDeep[0][0] = tmpShallow[2][0];
                tmpDeep[0][1] = tmpShallow[1][0];
                tmpDeep[0][2] = tmpShallow[0][0];
                tmpDeep[1][0] = tmpShallow[2][1];
                tmpDeep[1][2] = tmpShallow[0][1];
                tmpDeep[2][0] = tmpShallow[2][2];
                tmpDeep[2][1] = tmpShallow[1][2];
                tmpDeep[2][2] = tmpShallow[0][2];
                break;
            case 'R':
                tmpDeep[0][0] = tmpShallow[0][2];
                tmpDeep[0][1] = tmpShallow[1][2];
                tmpDeep[0][2] = tmpShallow[2][2];
                tmpDeep[1][0] = tmpShallow[0][1];
                tmpDeep[1][2] = tmpShallow[2][1];
                tmpDeep[2][0] = tmpShallow[0][0];
                tmpDeep[2][1] = tmpShallow[1][0];
                tmpDeep[2][2] = tmpShallow[2][0];
                break;
        }
        this.quadrants[quad] = tmpDeep;
    }

    /**
     * Checks whether a specific player has 5 in a row
     * @param mark Specific player
     * @return True if there is 5 in a row, false if not
     */
    public boolean hasRow(Mark mark) {
        return false;
    }

    /**
     * Checks whether a specific player has 5 in a column
     * @param mark Specific player
     * @return True if there is 5 in a column, false if not
     */
    public boolean hasColumn(Mark mark) {
        int fiveInACol = 0;
        for (int i = 0; i < (QUADRANT_NUM / 2) - 1; i++) {
            for (int j = 0; j < QUADRANT_SIZE - 1; j++) {

            }
        }
        return false;
    }

    /**
     * Checks whether a specific player has 5 diagonally
     * @param mark Specific player
     * @return True if there is 5 diagonally, false if not
     */
    public boolean hasDiagonal(Mark mark) {
        return false;
    }

    /**
     * Checks if a certain player has won
     * @param mark Specific player
     * @return True if there are 5 consecutive marks somewhere, false if not
     */
    public boolean isWinner(Mark mark) {
        return hasRow(mark) || hasColumn(mark) || hasDiagonal(mark);
    }

    /**
     * Checks whether the game has a winner
     * @return True if there is a winner, false if not
     */
    public boolean hasWinner() {
        return isWinner(Mark.BLACK) || isWinner(Mark.WHITE);
    }

    /**
     * Checks whether the game has ended
     * @return true if game has ended, false if not
     */
    public boolean gameOver() {
        return isFull() || hasWinner();
    }

    /**
     * Converts the board into a string representation
     * @return Board as a string
     */
    public String toString() {
        // TODO: Actually make this work
        return "";
    }

    /**
     * Sets a field on the board to be a certain mark
     * @param quad The quadrant to look at
     * @param x x position
     * @param y y position
     * @param mark Specific player
     */
    public void setField(int quad, int x, int y, Mark mark) {
        this.quadrants[quad][x][y] = mark;
    }

    /**
     * Translates coords in format [A-D][0-8] to 3 indexes and then calls itself with coords
     * @param userCoords [A-D][0-8]
     * @param mark Specific player
     */
    public void setField(String userCoords, Mark mark) {
        int[] coords = getCoords(userCoords);
        setField(coords[0], coords[1], coords[2], mark);
    }
}
