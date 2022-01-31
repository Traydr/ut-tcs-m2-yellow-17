package pentago.client.player;

import pentago.game_logic.Board;
import pentago.game_logic.Mark;

import java.io.InputStreamReader;
import java.util.Scanner;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

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

    @Override
    public String[] determineMove(Board board) {
        return new String[0];
    }
}
