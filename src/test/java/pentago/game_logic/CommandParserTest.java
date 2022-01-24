package pentago.game_logic;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class CommandParserTest {
    Board board;

    @BeforeEach
    void initialize() {
        board = new Board();
    }

    @Test
    void testClientToServer() {
        int[][] clientCoordinates = {{0, 0, 0}, {1, 2, 1}, {2, 2, 0}, {3, 2, 2}, {2, 1, 1}};
        int[] serverCoordinates = {0, 11, 20, 35, 25};

        for (int i = 0; i < clientCoordinates.length; i++) {
            assertEquals(serverCoordinates[i], CommandParser.clientToServer(clientCoordinates[i][0],
                                                                            clientCoordinates[i][1],
                                                                            clientCoordinates[i][2]));
        }
    }
}