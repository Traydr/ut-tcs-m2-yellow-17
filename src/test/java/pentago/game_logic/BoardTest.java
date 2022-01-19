package pentago.game_logic;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class BoardTest {
    Board board;

    @BeforeEach
    void initialize() {
        board = new Board();
    }

    @Test
    void testIfEmpty() {
        for (int i = 0; i < board.QUADRANT_NUM; i++) {
            for (int j = 0; j < board.QUADRANT_SIZE; j++) {
                for (int k = 0; k < board.QUADRANT_SIZE; k++) {
                    assertEquals(Mark.EMPTY, board.getField(i, j, k));
                }
            }
        }
    }

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

        // TODO: Test non-existing coordinates
    }

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
            boolean isField = board.isField(testCoordinates2[i][0], testCoordinates2[i][1], testCoordinates2[i][2]);
            assertEquals(expectedResults2[i], isField);
        }
    }

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
            board.setField(testCoordinates2[i][0], testCoordinates2[i][1], testCoordinates2[i][2], marks2[i]);
        }
        for (int i = 0; i < testCoordinates2.length; i++) {
            assertEquals(marks2[i], board.getField(testCoordinates2[i][0], testCoordinates2[i][1], testCoordinates2[i][2]));
        }
    }

    @Test
    void testIsEmptyField() {
        String[] testCoordinates1 = {"A4", "B2", "C6", "D4", "D8"};
        int[][] testCoordinates2 = {{0, 2, 1}, {1, 1, 1}, {2, 2, 1}, {3, 0, 1}};

        for (int i = 0; i < board.QUADRANT_NUM; i++) {
            for (int j = 0; j < board.QUADRANT_SIZE; j++) {
                for (int k = 0; k < board.QUADRANT_SIZE; k++) {
                    board.setField(i, j, k, Mark.BLACK);
                }
            }
        }

        for (int i = 0; i < testCoordinates1.length; i++) {
            board.setField(testCoordinates1[i], Mark.EMPTY);
        }
        for (int i = 0; i < testCoordinates2.length; i++) {
            board.setField(testCoordinates2[i][0], testCoordinates2[i][1], testCoordinates2[i][2], Mark.EMPTY);
        }

        for (var coordinate : testCoordinates1) {
            assertTrue(board.isEmptyField(coordinate));
        }
        for(var coordinate : testCoordinates2) {
            assertTrue(board.isEmptyField(coordinate[0], coordinate[1], coordinate[2]));
        }
    }
}
