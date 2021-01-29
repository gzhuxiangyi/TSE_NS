package test.test;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.junit.Test;

import spl.SPL;
import spl.fm.Product;
import spl.fm.TSet;

public class TestComputeProductsPartialCoverage {
    
    @Test
    public void test() {
        Product p1 = new Product();
        Product p2 = new Product();
        p1.addAll(new ArrayList<Integer>(Arrays.asList(1,2,3,4,5,6,7,8,-9,10,11,12,-13,14,-15,16,17,-18,19,20,21,22,23,-24)));
        p2.addAll(new ArrayList<Integer>(Arrays.asList(1,2,3,4,5,-6,7,8,-9,10,11,12,-13,14,-15,16,17,-18,19,20,21,22,23,-24)));
        List<Product> products = new ArrayList<>();
        products.add(p1);
        products.add(p2);
        TSet[] tSetArr = new TSet[10];
        tSetArr[0] = new TSet(new int[] {1,-9,10});
        tSetArr[1] = new TSet(new int[] {2,-5,-18});
        tSetArr[2] = new TSet(new int[] {3,6,20});
        tSetArr[3] = new TSet(new int[] {4,17,23});
        tSetArr[4] = new TSet(new int[] {5,-13,-24});
        tSetArr[5] = new TSet(new int[] {-6,7,17});
        tSetArr[6] = new TSet(new int[] {-7,9,11});
        tSetArr[7] = new TSet(new int[] {-8,18,20});
        tSetArr[8] = new TSet(new int[] {-9,20,21});
        tSetArr[9] = new TSet(new int[] {-10,-11,-23});
        Set<TSet> tSets = new HashSet<TSet>(){};
        for (TSet tSet : tSetArr) {
            tSets.add(tSet);
        }
        SPL.getInstance().computeProductsPartialCoverage(products, tSets);
        assertEquals(50, p1.getCoverage());
        assertEquals(10, p2.getCoverage());
    }

}
