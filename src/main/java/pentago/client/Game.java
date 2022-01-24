package pentago.client;

import pentago.client.player.Player;
import pentago.game_logic.Board;

public class Game {
    public static final int NUMBER_PLAYERS = 2;

    private final Board board;

    public Player[] players;

    private int current;

    public Game(Player p0, Player p1) {
        board = new Board();
        players = new Player[NUMBER_PLAYERS];
        players[0] = p0;
        players[1] = p1;
        current = 0;
    }

    private void play() {

    }

    /**
     * Resets the board. All fields will be set to {@code Mark.EMPTY}.
     */
    private void reset() {
        current = 0;
        board.reset();
    }

    /**
     * Updates the user on the current game situation by displaying the board.
     *
     * @return A string representing the board status
     */
    private String update() {
        return "\nCurrent game situation:\n" + board.toString() + "\n";
    }

    /**
     * Indicates the state of the game after it is over. For example, if it's a draw, this tells the
     * users that there is no winner.
     *
     * @return The result of the game after it is over
     */
    private String result() {
        if (board.hasWinner()) {
            Player winner = board.isWinner(players[0].getMark()) ? players[0] : players[1];
            return ("Player " + winner.getName() + " (" + winner.getMark().toString() +
                    ") has won!");
        } else {
            return "Draw. There is no winner!";
        }
    }
}
