package pentago.game_logic;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.RepeatedTest;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.*;

public class BoardTest {
    Board board;

    /**
     * Initializes an empty board before each test.
     */
    @BeforeEach
    void initialize() {
        board = new Board();
    }

    /**
     * Tests if the board only contains empty fields after initialization. This loops through all
     * fields one by one.
     */
    @Test
    void testIfEmpty() {
        for (int i = 0; i < board.quadrantNum; i++) {
            for (int j = 0; j < board.quadrantSize; j++) {
                for (int k = 0; k < board.quadrantSize; k++) {
                    assertEquals(Mark.EMPTY, board.getField(i, j, k));
                }
            }
        }
    }

    /**
     * Tests the conversion of user commands (A3, B1, C0) to coordinates ((0,0,1), (1,1,0), (2,0,
     * 0)).
     */
    @Test
    void testGetCoords() {
        String[] testUserCoordinates = {"A3", "B1", "C0", "D8", "B5"};
        int[][] correspondingCoordinates = {{0, 0, 1}, {1, 1, 0}, {2, 0, 0}, {3, 2, 2}, {1, 2, 1}};

        for (int i = 0; i < testUserCoordinates.length; i++) {
            int[] calculatedCoordinates = board.getCoords(testUserCoordinates[i]);
            assertEquals(correspondingCoordinates[i][0], calculatedCoordinates[0]);
            assertEquals(correspondingCoordinates[i][1], calculatedCoordinates[1]);
            assertEquals(correspondingCoordinates[i][2], calculatedCoordinates[2]);
        }

        assertNull(board.getCoords("A10"));
    }

    /**
     * Tests the isField method by looping through some existing and non-existing fields.
     */
    @Test
    void testIsField() {
        String[] testCoordinates1 = {"A4", "B2", "C3", "D9"};
        boolean[] expectedResults1 = {true, true, true, false};

        for (int i = 0; i < testCoordinates1.length; i++) {
            boolean isField = board.isField(testCoordinates1[i]);
            assertEquals(expectedResults1[i], isField);
        }

        int[][] testCoordinates2 = {{0, 4, 2}, {1, 2, 2}, {2, 1, 0}, {3, 2, 1}};
        boolean[] expectedResults2 = {false, true, true, true};

        for (int i = 0; i < testCoordinates2.length; i++) {
            boolean isField = board.isField(testCoordinates2[i][0], testCoordinates2[i][1],
                                            testCoordinates2[i][2]);
            assertEquals(expectedResults2[i], isField);
        }
    }

    /**
     * This tests the getField and setField methods. After a field has been set to a specific mark,
     * the getField method should return the same mark.
     */
    @Test
    void testGetSetFields() {
        String[] testCoordinates1 = {"A2", "B5", "C4", "D8"};
        Mark[] marks1 = {Mark.WHITE, Mark.WHITE, Mark.BLACK, Mark.BLACK};
        int[][] testCoordinates2 = {{0, 2, 1}, {1, 1, 1}, {2, 2, 1}, {3, 0, 1}};
        Mark[] marks2 = {Mark.BLACK, Mark.BLACK, Mark.WHITE, Mark.WHITE};

        for (int i = 0; i < testCoordinates1.length; i++) {
            board.setField(testCoordinates1[i], marks1[i]);
        }
        for (int i = 0; i < testCoordinates1.length; i++) {
            assertEquals(marks1[i], board.getField(testCoordinates1[i]));
        }

        for (int i = 0; i < testCoordinates2.length; i++) {
            board.setField(testCoordinates2[i][0], testCoordinates2[i][1], testCoordinates2[i][2],
                           marks2[i]);
        }
        for (int i = 0; i < testCoordinates2.length; i++) {
            assertEquals(marks2[i], board.getField(testCoordinates2[i][0], testCoordinates2[i][1],
                                                   testCoordinates2[i][2]));
        }
    }

    /**
     * Tests if a field is empty. This is done by setting all positions to a specific mark first,
     * and then setting some predefined coordinates to empty. Then the isEmptyField method should
     * return true at those specific coordinates.
     */
    @Test
    void testIsEmptyField() {
        String[] testCoordinates1 = {"A4", "B2", "C6", "D4", "D8"};
        int[][] testCoordinates2 = {{0, 2, 1}, {1, 1, 1}, {2, 2, 1}, {3, 0, 1}};

        for (int i = 0; i < board.quadrantNum; i++) {
            for (int j = 0; j < board.quadrantSize; j++) {
                for (int k = 0; k < board.quadrantSize; k++) {
                    board.setField(i, j, k, Mark.BLACK);
                }
            }
        }

        for (int i = 0; i < testCoordinates1.length; i++) {
            board.setField(testCoordinates1[i], Mark.EMPTY);
        }
        for (int i = 0; i < testCoordinates2.length; i++) {
            board.setField(testCoordinates2[i][0], testCoordinates2[i][1], testCoordinates2[i][2],
                           Mark.EMPTY);
        }

        for (var coordinate : testCoordinates1) {
            assertTrue(board.isEmptyField(coordinate));
        }
        for (var coordinate : testCoordinates2) {
            assertTrue(board.isEmptyField(coordinate[0], coordinate[1], coordinate[2]));
        }
    }

    /**
     * Tests if the board is filled. This test fills every position of the board, except the last
     * one. The function should of course return false. Then it also fills the last position, after
     * which the function should return true.
     */
    @Test
    void testIsFull() {
        // Fill the whole board, except for the very last value
        for (int i = 0; i < board.quadrantNum; i++) {
            for (int j = 0; j < board.quadrantSize; j++) {
                for (int k = 0; k < board.quadrantSize; k++) {
                    board.setField(i, j, k, new Random().nextBoolean() ? Mark.BLACK : Mark.WHITE);
                }
            }
        }
        board.setField(3, 2, 2, Mark.EMPTY); // Empty the last field

        assertFalse(board.isFull());

        board.setField(
                3, 2, 2, new Random().nextBoolean() ? Mark.BLACK :
                         Mark.WHITE); // Set the last field too

        assertTrue(board.isFull());
    }

    /**
     * This test checks the rotation of a quadrant by filling in some values, and then checking if
     * they are all in the correct place after a rotation.
     */
    @Test
    void testRotateQuadrant() {
        board.setField("A0", Mark.BLACK);
        board.setField("A1", Mark.WHITE);
        board.setField("A2", Mark.BLACK);
        board.setField("A3", Mark.WHITE);
        board.setField("A4", Mark.WHITE);
        board.setField("A5", Mark.BLACK);
        board.setField("A6", Mark.BLACK);
        board.setField("A7", Mark.WHITE);
        board.setField("A8", Mark.BLACK);

        board.rotateQuadrant("AL");

        assertEquals(Mark.BLACK, board.getField("A0"));
        assertEquals(Mark.BLACK, board.getField("A1"));
        assertEquals(Mark.BLACK, board.getField("A2"));
        assertEquals(Mark.WHITE, board.getField("A3"));
        assertEquals(Mark.WHITE, board.getField("A4"));
        assertEquals(Mark.WHITE, board.getField("A5"));
        assertEquals(Mark.BLACK, board.getField("A6"));
        assertEquals(Mark.WHITE, board.getField("A7"));
        assertEquals(Mark.BLACK, board.getField("A8"));
    }

    /**
     * Tests the hasRow method by realizing some predefined situations where the player is known to
     * have a row. The function should return true in these situations.
     */
    @Test
    void testHasRow() {
        String[] column1 = {"A1", "A2", "B0", "B1", "B2"};
        String[] column2 = {"C6", "C7", "C8", "D6", "D7"};
        String[] column3 = {"A3", "A4", "A5", "B3", "B4"};

        String[][] columns = {column1, column2, column3};

        for (var column : columns) {
            for (int i = 0; i < column.length; i++) {
                board.setField(column[i], Mark.BLACK);
            }
            assertTrue(board.hasRow(Mark.BLACK));
            board.reset(); // Make sure we reset the board
        }
    }

    /**
     * Tests the hasColumn method by realizing some predefined situations where the player is known
     * to have a column. The function should return true in these situations.
     */
    @Test
    void testHasColumn() {
        String[] column1 = {"A1", "A4", "A7", "C1", "C4"};
        String[] column2 = {"B2", "B5", "B8", "D2", "D5"};
        String[] column3 = {"A3", "A6", "C0", "C3", "C6"};

        String[][] columns = {column1, column2, column3};

        for (var column : columns) {
            for (int i = 0; i < column.length; i++) {
                board.setField(column[i], Mark.BLACK);
            }
            assertTrue(board.hasColumn(Mark.BLACK));
            board.reset(); // Make sure we reset the board
        }
    }

    /**
     * Tests the hasDiagonal method by realizing some predefined situations where the player is
     * known to have a diagonal. The function should return true in these situations.
     */
    @Test
    void testHasDiagonal() {
        String[][] columns = {{"A0", "A4", "A8", "D0", "D4"}, {"C4", "C2", "B6", "B4", "B2"},
                              {"C2", "D3", "A7", "A3", "D7"}};

        for (var column : columns) {
            for (int i = 0; i < column.length; i++) {
                board.setField(column[i], Mark.BLACK);
            }
            assertTrue(board.hasDiagonal(Mark.BLACK));
            board.reset(); // Make sure we reset the board
        }
    }

    /**
     * This test generates some boards where one player has 5 in a row. In this case, the
     * isWinner method should of course return true.
     */
    @Test
    void testIsWinner() {
        String[][] situations = {{"A1", "A2", "B0", "B1", "B2"}, {"B2", "B5", "B8", "D2", "D5"},
                                 {"A0", "A4", "A8", "D0", "D4"}};
        for (var situation : situations) {
            for (int i = 0; i < situation.length; i++) {
                board.setField(situation[i], Mark.BLACK);
            }
            assertTrue(board.isWinner(Mark.BLACK));
            board.reset(); // Make sure we reset the board
        }
    }

    /**
     * By setting the board to have 5 in a row for one player, this test checks if the hasWinner
     * method returns true in such cases.
     */
    @Test
    void testHasWinner() {
        String[][] situations = {{"A1", "A2", "B0", "B1", "B2"}, {"A3", "A6", "C0", "C3", "C6"},
                                 {"A3", "A4", "A5", "B3", "B4"}};
        for (var situation : situations) {
            for (int i = 0; i < situation.length; i++) {
                board.setField(situation[i], Mark.BLACK);
            }
            assertTrue(board.hasWinner());
            board.reset(); // Make sure we reset the board
        }
    }

    /**
     * This test first fills the board with random values. Then it empties some predefined fields,
     * after which the getEmptyFields is called. This should return the same list as the predefined
     * fields list (after we sort it).
     */
    @Test
    void testGetEmptyFields() {
        // Fill the whole board
        for (int i = 0; i < board.quadrantNum; i++) {
            for (int j = 0; j < board.quadrantSize; j++) {
                for (int k = 0; k < board.quadrantSize; k++) {
                    board.setField(i, j, k, new Random().nextBoolean() ? Mark.BLACK : Mark.WHITE);
                }
            }
        }

        // Empty some fields here
        String[] shouldBeEmpty = {"A0", "B2", "C4", "D8", "A3", "B1", "C7", "D0"};
        for (String field : shouldBeEmpty) {
            board.setField(field, Mark.EMPTY);
        }

        List<String> emptyFields = new ArrayList<>(List.of(shouldBeEmpty));
        Collections.sort(emptyFields);

        assertEquals(emptyFields, board.getEmptyFields());
    }

    /**
     * To test the toString method, a value on the board is set to the black mark. The string should
     * now contain a black mark string representation. Then a white mark is placed, now the string
     * should also include a white mark string.
     */
    @Test
    void testToString() {
        assertFalse(board.toString().contains(Mark.BLACK.toString()));
        assertFalse(board.toString().contains(Mark.WHITE.toString()));
        board.setField("A0", Mark.BLACK);
        assertTrue(board.toString().contains(Mark.BLACK.toString()));
        assertFalse(board.toString().contains(Mark.WHITE.toString()));
        board.setField("A1", Mark.WHITE);
        assertTrue(board.toString().contains(Mark.BLACK.toString()));
        assertTrue(board.toString().contains(Mark.WHITE.toString()));
    }

    /**
     * Checks the deepCopy method by looping through all values. It first generates a board with
     * random values. The copy should not be the same object, but the toString method should return
     * the same value, because the marks should still be the same.
     */
    @Test
    void testDeepCopy() {
        for (int i = 0; i < board.quadrantNum; i++) {
            for (int j = 0; j < board.quadrantSize; j++) {
                for (int k = 0; k < board.quadrantSize; k++) {
                    board.setField(i, j, k, new Random().nextBoolean() ? Mark.BLACK : Mark.WHITE);
                }
            }
        }

        Board copiedBoard = board.deepCopy();
        assertNotEquals(board, copiedBoard); // Check if it is not the same Object
        assertEquals(board.toString(), copiedBoard.toString()); // Check if the toString results
        // in the same output for both boards
    }

    /**
     * This test runs a randomly generated game. It is repeated 100 times to make sure that the
     * chances of having an edge case occur is very slim.
     */
    @RepeatedTest(100)
    void testFullGame() {
        Mark mark = Mark.BLACK;
        ArrayList<String> emptyFields;

        while (!board.gameOver()) {
            // Get a new random empty position in the field where we can place our mark
            emptyFields = board.getEmptyFields();
            String randomCoordinate = emptyFields.get(new Random().nextInt(emptyFields.size()));

            mark = (mark == Mark.BLACK) ? Mark.WHITE : Mark.BLACK; // Keep track of which mark
            // has to make a move
            board.setField(randomCoordinate, mark); // Set a random field to the selected mark

            char quadrant = (char) (new Random().nextInt(4) + 'A'); // Generate a random quadrant
            String direction = new Random().nextBoolean() ? "L" : "R"; // Generate a random
            // direction to rotate in

            board.rotateQuadrant(quadrant + direction);
        }
    }
}
