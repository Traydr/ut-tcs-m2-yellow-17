package pentago.client.player;

import pentago.game_logic.Board;
import pentago.game_logic.Mark;

public class Human extends Player {
    /**
     * Creates a new player object with a name and mark.
     *
     * @param name Name of the player
     * @param mark Mark of the player
     */
    /*@ requires name != null;
        requires mark == Mark.BLACK || mark == Mark.WHITE;
    @*/
    public Human(String name, Mark mark) {
        super(name, mark);
    }

    /**
     * Currently this method is not used when a human player is playing.
     *
     * @param board The current game board
     * @return an empty string array
     */
    public String[] determineMove(Board board) {
        return new String[0];
    }
}
