package pentago.client;

import pentago.client.player.Player;
import pentago.game_logic.Board;
import pentago.game_logic.CommandParser;
import pentago.game_logic.Mark;

import java.util.ArrayList;
import java.util.Random;

public class Game {
    public static final int NUMBER_PLAYERS = 2;

    public final Board board;

    public Player[] players;

    private int current;

    //TODO Check if it the local players turn
    public Game(Player p0, Player p1) {
        board = new Board();
        players = new Player[NUMBER_PLAYERS];
        players[0] = p0;
        players[1] = p1;
        current = 0;
    }

    /**
     * Resets the board. All fields will be set to {@code Mark.EMPTY}.
     */
    public void reset() {
        current = 0;
        board.reset();
    }

    public void listenerSetBoard(int pos, int rot) {
        int[] localCoords = CommandParser.protocolToLocalCoords(pos);
        board.setField(localCoords[0], localCoords[1], localCoords[2],
                       current % 2 == 0 ? Mark.BLACK : Mark.WHITE);
        current++;
        board.rotateQuadrant(CommandParser.protocolToLocalRotate(rot));
    }

    //    public boolean isCurrentPlayer(Player compare) {
    //        return players[current] == compare;
    //    }

    /**
     * Updates the user on the current game situation by displaying the board.
     *
     * @return A string representing the board status
     */
    public String update() {
        return board.toString() + "\n";
    }

    public String getRandomMove() {
        ArrayList<String> emptyFields = board.getEmptyFields();
        int arrSize = emptyFields.size();
        Random random = new Random();

        if (arrSize == 1) {
            return emptyFields.get(0);
        }
        return "Place: " + emptyFields.get(random.nextInt(arrSize)) + "\nRotate: " +
               CommandParser.protocolToLocalRotate(random.nextInt(8));
    }

    /**
     * Indicates the state of the game after it is over. For example, if it's a draw, this tells the
     * users that there is no winner.
     *
     * @return The result of the game after it is over
     */
    public String result() {
        if (board.hasWinner()) {
            Player winner = board.isWinner(players[0].getMark()) ? players[0] : players[1];
            return "Player " + winner.getName() + " (" + winner.getMark().toString() + ") has won!";
        } else {
            return "Draw. There is no winner!";
        }
    }
}
