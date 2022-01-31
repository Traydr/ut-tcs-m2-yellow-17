package pentago.client.player;

import pentago.game_logic.Board;
import pentago.game_logic.CommandParser;
import pentago.game_logic.Mark;

import java.util.ArrayList;
import java.util.Random;

public class SmartStrategy implements Strategy {
    /**
     * Returns the name of the smart bot.
     *
     * @return name of smart bot
     */
    @Override
    public String getName() {
        return "Smart-Bot";
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
        Board copiedBoard = board.deepCopy();
        ArrayList<String> emptyFields = board.getEmptyFields();
        int arrSize = emptyFields.size();

        // Try every possible move to check if it will result in a win
        for (int i = 0; i < arrSize; i++) {
            String field = emptyFields.get(i);
            copiedBoard.setField(field, mark);
            for (int j = 0; j < 8; j++) {
                String rotate = CommandParser.protocolToLocalRotate(j);
                copiedBoard.rotateQuadrant(rotate);
                if (copiedBoard.isWinner(mark)) {
                    return new String[]{field, rotate};
                }
                copiedBoard = board.deepCopy();
            }
        }

        // Check if the other player could win
        for (int i = 0; i < arrSize; i++) {
            String field = emptyFields.get(i);
            copiedBoard.setField(field, mark == Mark.BLACK ? Mark.WHITE : Mark.BLACK);
            for (int j = 0; j < 8; j++) {
                String rotate = CommandParser.protocolToLocalRotate(j);
                copiedBoard.rotateQuadrant(rotate);
                if (copiedBoard.isWinner(mark == Mark.BLACK ? Mark.WHITE : Mark.BLACK)) {
                    return new String[]{field, rotate};
                }
                copiedBoard = board.deepCopy();
            }
        }

        // We haven't found any winning move, so we should just get a random one
        return new String[]{arrSize < 1 ? emptyFields.get(0) :
                            emptyFields.get(new Random().nextInt(arrSize)),
                            CommandParser.protocolToLocalRotate(new Random().nextInt(8))};
    }
}
