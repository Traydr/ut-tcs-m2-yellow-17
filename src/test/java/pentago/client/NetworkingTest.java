package pentago.client;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class NetworkingTest {
    @Test
    void testIfOnePlusOneEqualsTwo() {
        assertEquals(Networking.oneplusone(), 2);
    }
}
