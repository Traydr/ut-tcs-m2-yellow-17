package pentago.client;

import pentago.client.player.Player;
import pentago.game_logic.Board;
import pentago.game_logic.CommandParser;
import pentago.game_logic.Mark;

import java.util.ArrayList;
import java.util.Random;

public class Game {
    private static final int NUMBER_PLAYERS = 2;
    private final Board board;
    private final Player[] players;
    private int current;

    /**
     * Game constructor.
     *
     * @param p0 player 1
     * @param p1 player 2
     */
    public Game(Player p0, Player p1) {
        board = new Board();
        players = new Player[NUMBER_PLAYERS];
        players[0] = p0;
        players[1] = p1;
        current = 0;
    }

    /**
     * Gets the board object.
     *
     * @return Board object
     */
    //@ requires board != null;
    public Board getBoard() {
        return board;
    }

    /**
     * Gets the current turn count.
     *
     * @return int count
     */
    //@ requires current >= 0;
    public int getCurrent() {
        return current;
    }

    /**
     * Sets the current turn counter.
     *
     * @param current a turn number
     */
    //@ requires current >= 0;
    public void setCurrent(int current) {
        this.current = current;
    }

    /**
     * Resets the board. All fields will be set to {@code Mark.EMPTY}.
     */
    //@ requires board != null;
    public void reset() {
        current = 0;
        board.reset();
    }

    /**
     * Sets a mark onto the board from the server.
     *
     * @param pos position of piece
     * @param rot rotation
     */
    //@ requires board != null;
    public void listenerSetBoard(int pos, int rot) {
        int[] localCoords = CommandParser.protocolToLocalCoords(pos);
        board.setField(localCoords[0], localCoords[1], localCoords[2],
                       current % 2 == 0 ? Mark.BLACK : Mark.WHITE);
        board.rotateQuadrant(CommandParser.protocolToLocalRotate(rot));
        current++;
    }

    /**
     * Updates the user on the current game situation by displaying the board.
     *
     * @param withHelp Whether the program should output an example board with the values
     * @return A string representing the board status
     */
    //@ requires board != null;
    public String update(boolean withHelp) {
        return board.toString(withHelp) + "\n";
    }

    /**
     * Updates the user on the current game situation by displaying the board.
     *
     * @return A string representing the board status
     */
    public String update() {
        return this.update(false);
    }

    /**
     * Gets a random move to be made.
     *
     * @return String in the form of "Place: [A-D][0-8] \n Rotate: [A-D][L|R]"
     */
    //@ requires board != null;
    //@ ensures \result != null;
    public String getRandomMove() {
        ArrayList<String> emptyFields = board.getEmptyFields();
        int arrSize = emptyFields.size();
        Random random = new Random();

        if (arrSize == 1) {
            return emptyFields.get(0);
        }
        return "Place: " + emptyFields.get(random.nextInt(arrSize)) + "\nRotate: " +
               CommandParser.protocolToLocalRotate(random.nextInt(8));
    }

    /**
     * Indicates the state of the game after it is over. For example, if it's a draw, this tells the
     * users that there is no winner.
     *
     * @return The result of the game after it is over
     */
    //@ requires board != null;
    //@ ensures \result != null;
    public String result() {
        if (board.hasWinner()) {
            Player winner = board.isWinner(players[0].getMark()) ? players[0] : players[1];
            return "Player " + winner.getName() + " (" + winner.getMark().toString() + ") has won!";
        } else {
            return "Draw. There is no winner!";
        }
    }

    /**
     * Returns if the game is over.
     *
     * @return true if game over, otherwise false
     */
    //@ requires board != null;
    //@ ensures \result == true || \result == false;
    public boolean isGameOver() {
        return board.gameOver();
    }
}
