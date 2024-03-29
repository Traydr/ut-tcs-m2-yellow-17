package pentago.server;

import pentago.game_logic.Board;
import pentago.game_logic.CommandParser;
import pentago.game_logic.Mark;

public class Game {
    public static final int NUMBER_PLAYERS = 2;
    private final Board board;
    private int current;
    private ClientHandler[] players;

    /**
     * Constructor for a new game object.
     *
     * @param player1 first player
     * @param player2 second player
     */
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
    //@ requires board != null;
    public void reset() {
        current = 0;
        board.reset();
    }

    /**
     * Sets a position on the board, while also checking to make sure that it is a valid move. Sends
     * an error back to the client if the move is incorrect. Sends a message to both clients if the
     * move went through.
     *
     * @param pos    The position where to place the mark
     * @param rot    Which square to rotate in which direction
     * @param player The player that made the move
     * @return true if the move went through, false if otherwise
     */
    //@ requires pos >= 0 && pos <= 35 && rot >= 0 && rot <= 8;
    //@ requires player != null;
    //@ requires board != null;
    public boolean setBoard(int pos, int rot, ClientHandler player) {
        if (player != players[current % 2]) {
            return false;
        }

        synchronized (board) {
            int[] localCoords = CommandParser.protocolToLocalCoords(pos);
            //Checks to make sure that the field that is being set is actually empty
            if (!board.isEmptyField(localCoords[0], localCoords[1], localCoords[2])) {
                player.sendError("This field is already occupied");
                return false;
            }

            //Sets the field, rotates and increases turn counter
            board.setField(localCoords[0], localCoords[1], localCoords[2],
                           current % 2 == 0 ? Mark.BLACK : Mark.WHITE);
            board.rotateQuadrant(CommandParser.protocolToLocalRotate(rot));
            current++;

            // Sends the message to the player that the move has been made
            for (ClientHandler p : players) {
                if (p.isAlreadyInGame() && p.isHasSentNewGame()) {
                    p.sendMessage("MOVE~" + pos + "~" + rot);
                }
            }
            // Checks if move has resulted in a win
            if (board.isFull() || board.hasWinner()) {
                checkWinner();
            }
            return true;
        }
    }

    /**
     * Indicates the state of the game after it is over. For example, if it's a draw, this tells the
     * users that there is no winner.
     *
     * @return The result of the game after it is over. {@code null} if there is no winner.
     */
    //@ ensures board.isWinner(Mark.BLACK) ==> \result == Mark.BLACK;
    //@ ensures board.isWinner(Mark.WHITE) ==> \result == Mark.WHITE;
    //@ ensures (board.hasWinner() == false) ==> \result == null;
    public Mark winner() {
        return board.hasWinner() ? (board.isWinner(Mark.BLACK) ? Mark.BLACK : Mark.WHITE) : null;
    }

    /**
     * Gets the player that disconnected and sends a gameover message to the other player. It also
     * ends the game.
     *
     * @param discPlayer the player that disconnected
     */
    //@ requires discPlayer != null;
    public void winByDisconnect(ClientHandler discPlayer) {
        if (players[0] == discPlayer) {
            players[1].sendMessage("GAMEOVER~DISCONNECT~" + players[1].getUsername());
            players[1].endGame();
        } else if (players[1] == discPlayer) {
            players[0].sendMessage("GAMEOVER~DISCONNECT~" + players[0].getUsername());
            players[0].endGame();
        }
    }

    /**
     * Checks if there is a winner, it does nothing if there is no winner and the board is not full.
     * Otherwise, it responds with the corresponding game over message.
     */
    //@ requires board != null;
    public void checkWinner() {
        synchronized (board) {
            // If the board isn't full or doesn't have a winner immediately return
            if (!board.hasWinner() && !board.isFull()) {
                return;
            }
            Mark mWinner = winner();

            // This is to check if there is a draw
            if (!board.hasWinner() && board.isFull()) {
                for (ClientHandler player : players) {
                    player.sendMessage("GAMEOVER~DRAW");
                    player.endGame();
                }
                return;
            }

            // Checks which client won
            ClientHandler output = mWinner == Mark.BLACK ? players[0] : players[1];
            for (ClientHandler player : players) {
                player.sendMessage("GAMEOVER~VICTORY~" + output.getUsername());
                player.endGame();
            }
            return;
        }
    }
}
