package pentago.server;

import pentago.client.player.Player;
import pentago.game_logic.Board;
import pentago.game_logic.CommandParser;
import pentago.game_logic.Mark;

public class Game {
    public static final int NUMBER_PLAYERS = 2;
    private final Board board;
    private int current;
    private ClientHandler[] players;

    public Game(ClientHandler player1, ClientHandler player2) {
        board = new Board();
        players = new ClientHandler[NUMBER_PLAYERS];
        players[0] = player1;
        players[1] = player2;
        current = 0;
    }

    /**
     * Resets the board. All fields will be set to {@code Mark.EMPTY}.
     */
    public void reset() {
        current = 0;
        board.reset();
    }

    /**
     * Actually make a move in the board.
     * @param pos The integer representation of the place in the board (See protocol documentation)
     * @param rot The integer representation of the rotation (See protocol documentation)
     * @return true if move went through, false if not
     */
    public boolean setBoard(int pos, int rot, ClientHandler player) {
        if (player != players[current % 2]) {
            return false;
        }

        int[] localCoords = CommandParser.protocolToLocalCoords(pos);
        board.setField(localCoords[0], localCoords[1], localCoords[2],
                       current % 2 == 0 ? Mark.BLACK : Mark.WHITE);
        current++;
        board.rotateQuadrant(CommandParser.protocolToLocalRotate(rot));
        return true;
    }

    /**
     * Indicates the state of the game after it is over. For example, if it's a draw, this tells the
     * users that there is no winner.
     *
     * @return The result of the game after it is over. {@code null} if there is no winner.
     */
    public Mark winner() {
        return board.hasWinner() ? (board.isWinner(Mark.BLACK) ? Mark.BLACK : Mark.WHITE) : null;
    }
}
