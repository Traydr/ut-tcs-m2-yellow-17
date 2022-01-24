package pentago.client.player;

import pentago.game_logic.Board;
import pentago.game_logic.Mark;

public class Bot extends Player {
    /**
     * Creates a new player object with a name and mark.
     *
     * @param name Name of the player
     * @param mark Mark of the player
     */
    /*@ requires name != null;
        requires mark == Mark.BLACK || mark == Mark.WHITE;
    @*/
    public Bot(String name, Mark mark) {
        super(name, mark);
    }

    @Override
    public String determineMove(Board board) {
        return null;
    }

    @Override
    public String determineRotate(Board board) {
        return null;
    }
}
