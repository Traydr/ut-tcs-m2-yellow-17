package test.java;

import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class MyTest {
    @Test
    public void onePlusOneShouldBeTwo() {
        int sum = 1 + 1;
        assertEquals(3, sum);
    }
}
