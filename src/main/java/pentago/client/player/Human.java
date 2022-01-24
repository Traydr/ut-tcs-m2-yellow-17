package pentago.client.player;

import pentago.game_logic.Board;
import pentago.game_logic.Mark;

import java.io.InputStreamReader;
import java.nio.file.LinkPermission;
import java.util.Scanner;

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
    public String determineMove(Board board) {
        String input;
        try (Scanner scanner = new Scanner(new InputStreamReader(System.in))){
            String prompt = "> " + getName() + " (" + getMark().toString() + ")"
                            + ", what is your choice? ";

            System.out.println(prompt);
            input = scanner.nextLine();

            boolean valid = board.isField(input) && board.isEmptyField(input);
            while (!valid) {
                System.out.println("ERROR: field " + input + " is no valid choice.");
                System.out.println(prompt);
                input = scanner.nextLine();
                valid = board.isField(input) && board.isEmptyField(input);
            }
        }
        return input;
    }
}
