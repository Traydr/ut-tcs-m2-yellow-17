package pentago.client.player;

import pentago.game_logic.Board;
import pentago.game_logic.Mark;

public interface Strategy {
    public String getName();
    public String determineMove(Board board, Mark mark);
    public String determineRotate(Board board, Mark mark);
}
