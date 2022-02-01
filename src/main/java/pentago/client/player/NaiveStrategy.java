package pentago.client.player;

import pentago.game_logic.Board;
import pentago.game_logic.CommandParser;
import pentago.game_logic.Mark;

import java.util.ArrayList;
import java.util.Random;

public class NaiveStrategy implements Strategy {
    /**
     * Returns the name of the naive bot.
     *
     * @return name of naive bot
     */
    @Override
    public String getName() {
        return "Naive-Bot";
    }

    /**
     * Return the string coords of the move it wants to make.
     *
     * @param board The current game board
     * @param mark  The bots mark
     * @return [A-D][0-8] coordinate together with [A-D][L|R] rotate
     */
    @Override
    public String[] determineMove(Board board, Mark mark) {
        ArrayList<String> emptyFields = board.getEmptyFields();
        int arrSize = emptyFields.size();
        Random random = new Random();

        return new String[]{
            arrSize < 1 ? emptyFields.get(0) : emptyFields.get(random.nextInt(arrSize)),
            CommandParser.protocolToLocalRotate(random.nextInt(8))};
    }
}
