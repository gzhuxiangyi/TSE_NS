package test.test;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.Test;

import spl.techniques.DistancesUtil;

public class TestMinFastSort {
    
    @Test
    public void testMinFastSort() {
        double[] x = {8,7,3,5,6,4,1,2};
        int[] idx = {1,2,3,4,5,6,7,8};
        DistancesUtil.minFastSort(x, idx , 8, 6);
        // for (int i = 0; i < idx.length; i++) {
            // System.out.println(x[i] + " " + idx[i]);
        // }
        assertEquals(x[0], 1.0);
        assertEquals(x[1], 2.0);
        assertEquals(x[2], 3.0);
        assertEquals(x[3], 4.0);
        assertEquals(x[4], 5.0);
        assertEquals(x[5], 6.0);
        assertEquals(idx[0], 7);
        assertEquals(idx[1], 8);
        assertEquals(idx[2], 3);
        assertEquals(idx[3], 6);
        assertEquals(idx[4], 4);
        assertEquals(idx[5], 5);

        double[] y = {8,7,3,5,6,4,1,2};
        int[] idy = {1,2,3,4,5,6,7,8};
        DistancesUtil.minFastSort(y, idy , 8, 4);
        assertEquals(y[0], 1.0);
        assertEquals(y[1], 2.0);
        assertEquals(y[2], 3.0);
        assertEquals(y[3], 4.0);
        assertEquals(idy[0], 7);
        assertEquals(idy[1], 8);
        assertEquals(idy[2], 3);
        assertEquals(idy[3], 6);
    }
}
