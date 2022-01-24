package pentago.client.player;

import pentago.game_logic.Board;
import pentago.game_logic.Mark;

public class NaiveStrategy implements Strategy {
    @Override
    public String getName() {
        return "Naive-Bot";
    }

    @Override
    public String determineMove(Board board, Mark mark) {
        return "";
    }
}
