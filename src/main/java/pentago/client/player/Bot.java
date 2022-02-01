package pentago.client.player;

import pentago.game_logic.Board;
import pentago.game_logic.Mark;

public class Bot extends Player {
    Mark mark;
    Strategy strategy;

    /**
     * Creates a new Bot object with a specified strategy.
     *
     * @param mark
     * @param strategy
     */
    /*@ requires mark == Mark.BLACK || mark == Mark.WHITE;
        requires strategy != null;
        ensures this.mark != null && this.strategy != null;
    @*/
    public Bot(Mark mark, Strategy strategy) {
        super(strategy.getName() + "-" + mark.toString(), mark);
        this.mark = mark;
        this.strategy = strategy;
    }

    /**
     * Creates a new Bot object with a mark and the naive strategy.
     *
     * @param mark Mark of the player
     */
    /*@ requires mark == Mark.BLACK || mark == Mark.WHITE;
        ensures this.mark != null || this.strategy instanceof NaiveStrategy;
    @*/
    public Bot(Mark mark) {
        this(mark, new NaiveStrategy());
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
    public String[] determineMove(Board board) {
        return strategy.determineMove(board, this.mark);
    }
}
