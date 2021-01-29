/*
 * Author : Christopher Henard (christopher.henard@uni.lu)
 * Date : 21/05/2012
 * Copyright 2012 University of Luxembourg – Interdisciplinary Centre for Security Reliability and Trust (SnT)
 * All rights reserved
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.

 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.

 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package spl.techniques;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import spl.fm.Product;

/**
 * This class defines some common normalized distances to measure the 
 * distance between two products.
 * 计算距离：完全看懂
 *  
 * @author Christopher Henard
 */
public class DistancesUtil {

    public static double getSetBasedDistance(Product p1, Product p2, double weight) {
        Set<Integer> intersection = new HashSet<Integer>(p1);
        Set<Integer> union = new HashSet<Integer>(p1);
        intersection.retainAll(p2);
        union.addAll(p2);
        double intersectionSize = intersection.size();
        double unionSize = union.size();

        return 1.0 - (intersectionSize / (intersectionSize + weight * (unionSize - intersectionSize)));
    }

    public static int getSetBasedDifference(Product p1, Product p2) {
        Set<Integer> intersection = new HashSet<Integer>(p1);
        intersection.retainAll(p2);
        return p1.size() - intersection.size();
    }
    
    public static double getJaccardDistance(Product p1, Product p2) {
        return getSetBasedDistance(p1, p2, 1.0);
    }

    // Also known as Gower-Legendre.
    public static double getDiceDistance(Product p1, Product p2) {
        return getSetBasedDistance(p1, p2, 0.5);
    }

    // Also known as Sokal-Sneath.
    public static double getAntiDiceDistance(Product p1, Product p2) {
        return getSetBasedDistance(p1, p2, 2.0);
    }

    
    public static double getHammingDistance (Product p1, Product p2) {
  	    Set<Integer> intersection = new HashSet<Integer>(p1);
        intersection.retainAll(p2);         
        double intersectionSize = intersection.size();            

        return 1.0 - intersectionSize / p1.size();
        
    }
    
    public static double getDiffPairs(Product p1, Product p2) {
        int size = p1.size();
        int max = size * (size - 1) / 2;

        boolean[] pb1 = productToBits(p1);
        boolean[] pb2 = productToBits(p2);

        int same = nSameBits(pb1, pb2);
        return max - same * (same - 1) / 2;


    }
    

    public static boolean[] productToBits(Product product) {
        boolean[] res = new boolean[product.size()];
        List<Integer> li = new ArrayList<Integer>(product);

        Collections.sort(li, new Comparator<Integer>() {

            @Override
            public int compare(Integer o1, Integer o2) {
                return Double.compare(Math.abs(o1), Math.abs(o2));
            }
        });

        int n = 0;
        for (Integer i : li) {
            res[n++] = (i > 0);

        }
        return res;
    }

    public static int nSameBits(boolean[] p1, boolean[] p2) {

        int n = 0;
        for (int i = 0; i < p1.length; i++) {
            if (p1[i] == p2[i]) {
                n++;
            }

        }
        return n;
    }
    
    public static void minFastSort(double x[], int idx[], int n, int m) {
        for (int i = 0; i < m; i++) {
            for (int j = i + 1; j < n; j++) {
                if (x[i] > x[j]) {
                    double temp = x[i];
                    x[i]   = x[j];
                    x[j]   = temp;
                    int id = idx[i];
                    idx[i] = idx[j];
                    idx[j] = id;
                } // if
            }
        } // for

    } // minFastSort

    public static void maxFastSort(double x[], int idx[], int n, int m) {
        for (int i = 0; i < m; i++) {
            for (int j = i + 1; j < n; j++) {
                if (x[i] < x[j]) {
                    double temp = x[i];
                    x[i]   = x[j];
                    x[j]   = temp;
                    int id = idx[i];
                    idx[i] = idx[j];
                    idx[j] = id;
                } // if
            }
        } // for

    } // maxFastSort
    
 } // 

