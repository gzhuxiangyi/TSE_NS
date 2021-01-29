package test.test;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.ArrayList;
import java.util.Arrays;

import org.junit.Test;

import spl.fm.Product;
import spl.techniques.DistancesUtil;

public class TestGetAntiDiceDistance {
    @Test
    public void testGetAntiDiceDistance() {
        Product p1 = new Product();
        Product p2 = new Product();
        p1.addAll(new ArrayList<Integer>(Arrays.asList(1,2,-3)));
        p2.addAll(new ArrayList<Integer>(Arrays.asList(1,-2,3)));
        Double d1 = DistancesUtil.getAntiDiceDistance(p1, p2);
        assertEquals(8/9.0, d1, 1e-6);


        p1.clear();
        p2.clear();
        p1.addAll(new ArrayList<Integer>(Arrays.asList(1,-2,3,4,-5)));
        p2.addAll(new ArrayList<Integer>(Arrays.asList(1,2,-3,4,5)));
        Double d2 = DistancesUtil.getAntiDiceDistance(p1, p2);
        assertEquals(6/7.0, d2, 1e-6);

        p1.clear();
        p2.clear();
        p1.addAll(new ArrayList<Integer>(Arrays.asList(1,2,3,4,5,6,7,8,9)));
        p2.addAll(new ArrayList<Integer>(Arrays.asList(-1,-2,-3,-4,-5,-6,-7,-8,-9)));
        Double d3 = DistancesUtil.getAntiDiceDistance(p1, p2);
        assertEquals(1, d3, 1e-6);

        p1.clear();
        p2.clear();
        p1.addAll(new ArrayList<Integer>(Arrays.asList(1,2,3,4,5,6)));
        p2.addAll(new ArrayList<Integer>(Arrays.asList(1,2,3,4,5,6)));
        Double d4 = DistancesUtil.getAntiDiceDistance(p1, p2);
        assertEquals(0, d4, 1e-6);
    }
}
