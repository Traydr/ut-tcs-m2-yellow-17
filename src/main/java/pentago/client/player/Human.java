package pentago.client.player;

import pentago.game_logic.Board;
import pentago.game_logic.Mark;

import java.io.InputStreamReader;
import java.util.Scanner;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

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
    public String[] determineMove(Board board) {
        String input;
        Pattern pattern = Pattern.compile("[A-D][0-8]");
        Matcher matcher;
        try (Scanner scanner = new Scanner(new InputStreamReader(System.in))) {
            String prompt = "> " + getName() + " (" + getMark().toString() + ")"
                            + ", what is your choice? [A-D][0-8]";

            System.out.println(prompt);
            input = scanner.nextLine();

            matcher = pattern.matcher(input);
            boolean valid = board.isField(input) && board.isEmptyField(input) &&
                            matcher.find() && input.length() == 2;
            while (!valid) {
                System.out.println("ERROR: field " + input + " is no valid choice.");
                System.out.println(prompt);
                input = scanner.nextLine();
                matcher = pattern.matcher(input);
                valid = board.isField(input) && board.isEmptyField(input) &&
                        matcher.find() && input.length() == 2;
            }
        }



        String rotateInput;
        Pattern rotatePattern = Pattern.compile("[A-D][L|R]");
        Matcher rotateMatcher;

        try (Scanner scanner = new Scanner(new InputStreamReader(System.in))) {
            String prompt = "> " + getName() + " (" + getMark().toString() + ")"
                            + ", rotation? [A-D][L|R] ";

            System.out.println(prompt);
            rotateInput = scanner.nextLine();

            rotateMatcher = rotatePattern.matcher(rotateInput);
            boolean valid = rotateMatcher.find() && rotateInput.length() == 2;
            while (!valid) {
                System.out.println("ERROR: field " + rotateInput + " is no valid choice.");
                System.out.println(prompt);
                rotateInput = scanner.nextLine();
                rotateMatcher = rotatePattern.matcher(rotateInput);
                valid = rotateMatcher.find() && rotateInput.length() == 2;
            }
        }

        return new String[]{input, rotateInput};
    }
}
