package pentago.client.player;

import pentago.game_logic.Board;
import pentago.game_logic.Mark;

public abstract class Player {
    private final String name;
    private final Mark mark;

    /**
     * Creates a new player object with a name and mark.
     *
     * @param name Name of the player
     * @param mark Mark of the player
     */
    /*@ requires name != null;
        requires mark == Mark.BLACK || mark == Mark.WHITE;
        ensures this.name == name;
        ensures this.mark == mark;
    @*/
    public Player(String name, Mark mark) {
        this.name = name;
        this.mark = mark;
    }

    /**
     * Returns the name of the player.
     *
     * @return Player name
     */
    public String getName() {
        return name;
    }

    /**
     * Returns the mark of the player.
     *
     * @return Player mark
     */
    public Mark getMark() {
        return mark;
    }

    /**
     * Determines the field for the next move.
     *
     * @param board The current game board
     * @return the players' choice
     */
    /*@ requires board != null && board.isFull() == false;
        ensures board.isField(\result) && board.getField(\result) == Mark.EMPTY;
    @*/

    public abstract String[] determineMove(Board board);

    /**
     * Determines the next rotate.
     *
     * @param board the current game board.
     * @return rotate in form [A-D][L|R]
     */
    public abstract String determineRotate(Board board);

    /**
     * Makes a move on the board.
     *
     * @param board the current board
     */
    public void makeMove(Board board) {
        String[] move = determineMove(board);
        board.setField(move[0], getMark());
        board.rotateQuadrant(move[1]);
    }
}
