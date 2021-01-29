package test.test;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.Before;
import org.junit.Test;

import spl.techniques.ns.NoveltySearch1plusN;

public class TestBinarySelection {

    private NoveltySearch1plusN ns;

    @Before
    public void setUp() {
        ns = new NoveltySearch1plusN(10,20,0.1,100000,0.0);
        double[] scores = {2,5,4,6,8,7,1,4,10,9};
        ns.setNoveltyScores(scores);
    }

    @Test
    public void testBinarySelection() {
        int x1 = ns.binarySelection(5, 7);
        int x2 = ns.binarySelection(8, 3);
        assertEquals(5, x1);
        assertEquals(8, x2);
    }
}
