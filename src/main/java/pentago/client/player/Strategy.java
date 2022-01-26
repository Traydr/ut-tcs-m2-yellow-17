package pentago.client.player;

import pentago.game_logic.Board;
import pentago.game_logic.Mark;

public interface Strategy {
    /**
     * Gets the name of the strategy.
     * @return name
     */
    String getName();

    /**
     * Determines the next move to make.
     * @param board the current board
     * @param mark the mark of the strategy
     * @return the next move in [A-D][0-8] and rotate in [A-D][L|R]
     */
    String[] determineMove(Board board, Mark mark);
}
