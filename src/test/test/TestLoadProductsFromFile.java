package test.test;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import org.junit.Test;

import spl.SPL;
import spl.fm.Product;

public class TestLoadProductsFromFile {
    @Test
    public void testLoadProducts() throws IOException {
        String inFile = "./test/resource/Products.0";
        List<Product> products = new ArrayList();
        try {
            products = SPL.getInstance().loadProductsFromFile(inFile);
        } catch (Exception e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        assertEquals(products.get(0).toString(), "[1, 2, 3, 4, 5, 6, 7, 8, -9, 10, 11, 12, -13, 14, -15, 16, 17, -18, 19, 20, 21, 22, 23, -24]");
        assertEquals(products.get(99).toString(), "[1, 2, 3, 4, 5, -6, 7, -8, -9, 10, -11, -12, -13, -14, -15, 16, 17, 18, 19, 20, 21, -22, 23, 24]");
        assertEquals(products.size(), 100);
    }
}
