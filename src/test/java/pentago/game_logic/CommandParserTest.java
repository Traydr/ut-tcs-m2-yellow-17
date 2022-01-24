package pentago.game_logic;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;

public class CommandParserTest {
    Board board;

    @BeforeEach
    void initialize() {
        board = new Board();
    }

    @Test
    void testLocalToiProtocolCoords() {
        int[][] clientCoordinates = {{0, 0, 0}, {1, 2, 1}, {2, 2, 0}, {3, 2, 2}, {2, 1, 1}};
        int[] serverCoordinates = {0, 11, 20, 35, 25};

        for (int i = 0; i < clientCoordinates.length; i++) {
            assertEquals(serverCoordinates[i],
                         CommandParser.localToProtocolCoords(clientCoordinates[i][0],
                                                             clientCoordinates[i][1],
                                                             clientCoordinates[i][2]));
        }
    }

    @Test
    void testProtocolToLocalCoords() {
        int[] serverCoordinates = {0, 11, 20, 35, 25, 3, 14, 17, 18, 32, 21, 35};
        int[][] clientCoordinates =
                {{0, 0, 0}, {1, 2, 1}, {2, 2, 0}, {3, 2, 2}, {2, 1, 1}, {1, 0, 0}, {0, 2, 2},
                 {1, 2, 2}, {2, 0, 0}, {2, 2, 2}, {3, 0, 0}, {3, 2, 2}};

        for (int i = 0; i < serverCoordinates.length; i++) {
            assertArrayEquals(clientCoordinates[i],
                              CommandParser.protocolToLocalCoords(serverCoordinates[i]));
        }
    }

    String[] localRotationCommands = {"AL", "AR", "BL", "BR", "CL", "CR", "DL", "DR"};
    int[] protocolRotationCommands = {0, 1, 2, 3, 4, 5, 6, 7};

    @Test
    void testLocalToProtocolRotate() {
        for (int i = 0; i < localRotationCommands.length; i++) {
            assertEquals(
                    protocolRotationCommands[i],
                    CommandParser.localToProtocolRotate(localRotationCommands[i]));
        }
    }

    @Test
    void testProtocolToLocalRotate() {
        for (int i = 0; i < protocolRotationCommands.length; i++) {
            assertEquals(
                    localRotationCommands[i],
                    CommandParser.protocolToLocalRotate(protocolRotationCommands[i]));
        }
    }
}