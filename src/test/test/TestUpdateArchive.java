package test.test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import spl.SPL;
import spl.fm.Product;
import spl.techniques.ns.NoveltySearch1plusN;

public class TestUpdateArchive {

    private NoveltySearch1plusN ns;

    public void setArchive(String inFile) {
        ns = new NoveltySearch1plusN(100,20,0.0,100000,0.1);

        List<Product> products = new ArrayList();
        try {
            products = SPL.getInstance().loadProductsFromFile(inFile);
        } catch (Exception e) {
            e.printStackTrace();
        }

        ns.setArchive(products);
    }

    @Test
    // 1.The archive contains this product. 
    public void test1() {

        String inFile = "./src/test/resource/Products.0";
        setArchive(inFile);
       
        Product p = new Product();
        p.addAll(new ArrayList<Integer>(Arrays.asList(1, 2, 3, 4, 5, 6, 7, 8, -9, 10, 11, 12, -13, 14, -15, 16, 17, -18, 19, 20, 21, 22, 23, -24)));
        boolean b = ns.updateAchive(p);
        assertFalse(b);
        boolean containP = false;
        for (Product product: ns.getArchive()) {
            if (product.toString().equals(p.toString())) containP = true;
        }
        assertTrue(containP);
        assertEquals(100, ns.getArchive().size()); 

    }

    @Test
    //  2.The size of the archive is not full
    public void test2() {

        String inFile = "./src/test/resource/Products.1";
        setArchive(inFile);

        Product p = new Product();
        p.addAll(new ArrayList<Integer>(Arrays.asList(1,2,3,4,5,-6,7,-8,-9,10,-11,-12,-13,-14,-15,16,17,18,19,20,21,-22,23,24)));
        boolean b = ns.updateAchive(p);
        assertTrue(b);
        boolean containP = false;
        for (Product product: ns.getArchive()) {
            if (product.toString().equals(p.toString())) containP = true;
        }
        assertTrue(containP);
        assertEquals(100, ns.getArchive().size());

    }

    @Test
    //  3.The novelty score is smaller, do not replace
    public void test3() {

        String inFile = "./src/test/resource/Products.2";
        setArchive(inFile);

        Product p = new Product();
        p.addAll(new ArrayList<Integer>(Arrays.asList(1,2,3,4,5,6,7,8,-9,10,11,12,13,14,15,16,17,-18,19,20,21,22,23,24)));
        boolean b = ns.updateAchive(p);
        boolean containP = false;
        for (Product product: ns.getArchive()) {
            if (product.toString().equals(p.toString())) containP = true;
        }
        assertTrue(containP);
        assertTrue(b);
        assertEquals(100, ns.getArchive().size());
    }

    @Test
    //  3.The novelty score is larger, replace
    public void test4() {
        String inFile = "./src/test/resource/Products.0";
        setArchive(inFile);

        Product p = new Product();
        p.addAll(new ArrayList<Integer>(Arrays.asList(1,2,3,4,5,6,7,8,-9,10,11,12,-13,14,-15,16,17,18,19,20,21,22,23,-24)));
        boolean b = ns.updateAchive(p);
        boolean containP = false;
        for (Product product: ns.getArchive()) {
            if (product.toString().equals(p.toString())) containP = true;
        }
        assertFalse(containP);
        assertFalse(b);
        assertEquals(100, ns.getArchive().size());
    }

}
