package pentago.server;

import pentago.game_logic.Board;
import pentago.game_logic.CommandParser;
import pentago.game_logic.Mark;

public class Game {
    public static final int NUMBER_PLAYERS = 2;
    private final Board board;
    private int current;
    private ClientHandler[] players;

    //TODO Redo java doc
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
        if (!board.isEmptyField(localCoords[0], localCoords[1], localCoords[2])) {
            player.sendError("This field is already occupied");
            return false;
        }

        board.setField(localCoords[0], localCoords[1], localCoords[2],
                       current % 2 == 0 ? Mark.BLACK : Mark.WHITE);
        current++;
        board.rotateQuadrant(CommandParser.protocolToLocalRotate(rot));

        for (ClientHandler p : players) {
            p.sendMessage("MOVE~" + pos + "~" + rot);
        }
        checkWinner();
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

    public void winByDisconnect(ClientHandler discPlayer) {
        if (players[0] == discPlayer) {
            players[1].sendMessage("GAMEOVER~DISCONNECT~" + players[1].getUsername());
            players[1].endGame();
        } else if (players[1] == discPlayer) {
            players[0].sendMessage("GAMEOVER~DISCONNECT~" + players[0].getUsername());
            players[0].endGame();
        }
    }

    public void checkWinner() {
        if (!board.hasWinner() && !board.isFull()) {
            return;
        }
        Mark mWinner = winner();

        if (!board.hasWinner() && board.isFull()) {
            for (ClientHandler player : players) {
                player.sendMessage("GAMEOVER~DRAW");
                player.endGame();
            }
            return;
        }

        ClientHandler output = mWinner == Mark.BLACK ? players[0] : players[1];
        for (ClientHandler player : players) {
            player.sendMessage("GAMEOVER~VICTORY~" + output.getUsername());
            player.endGame();
        }
        return;
    }
}
