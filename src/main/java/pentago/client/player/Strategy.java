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
     * @return the next move in [A-D][0-8]
     */
    String determineMove(Board board, Mark mark);

    /**
     * Determines the next rotate to make.
     * @param board the current board
     * @param mark the mark of the strategy
     * @return the next rotate in [A-D][L|R]
     */
    String determineRotate(Board board, Mark mark);
}
