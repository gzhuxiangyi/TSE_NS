/*
 * Author : Yi Xiang
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
package spl.techniques.pdda;

import java.io.FileOutputStream;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Random;

import spl.SPLSnapshoot;
import spl.fm.Product;

/**
 *
 * @author Yi Xiang
 * 
 * This class represents the PD driven algorithm for the test problem
 */
public class PDDrivenAlgorithm {

    private static Random random;
    private long timeAllowedMS;

    public PDDrivenAlgorithm(long timeAllowedMS) {
        this.timeAllowedMS = timeAllowedMS;
        random = new Random();
    }

    public static List<Integer> productToList(Product product) {
        List<Integer> li = new ArrayList<Integer>(product);

        Collections.sort(li, new Comparator<Integer>() {

            @Override
            public int compare(Integer o1, Integer o2) {
                return Double.compare(Math.abs(o1), Math.abs(o2));
            }
        });


        return li;
    }



   
    public Individual crossover(Individual indiv1, Individual indiv2) {

        Individual offspring1, offspring2;

        int crossPoint = (int) (Math.random() * (indiv1.getSize() - 1)) + 1;
        offspring1 = new Individual(indiv1);
        offspring2 = new Individual(indiv2);

        boolean b = random.nextBoolean();

        if (b) {
            for (int i = crossPoint; i < offspring1.getSize(); i++) {
                Product p = offspring1.getProducts().get(i);
                offspring1.getProducts().set(i, offspring2.getProducts().get(i));
                offspring2.getProducts().set(i, p);
            }
        } else {
            for (int i = 0; i <= crossPoint; i++) {
                Product p = offspring1.getProducts().get(i);
                offspring1.getProducts().set(i, offspring2.getProducts().get(i));
                offspring2.getProducts().set(i, p);
            }
        }

        offspring1.fitnessAndOrdering();
        offspring2.fitnessAndOrdering();

        if (offspring1.getFitness() > offspring2.getFitness()) {
            return offspring1;
        } else if (offspring1.getFitness() < offspring2.getFitness()) {
            return offspring2;
        } else {
            b = random.nextBoolean();
            return b ? offspring1 : offspring2;
        }
    }

    public Individual runSimplePD(int individualSize, int mutateType) throws Exception {
        long startTimeMS = System.currentTimeMillis();
        Individual indiv = new Individual(SPLSnapshoot.getInstance().getUnpredictableProducts(individualSize));
        indiv.PDfitnessAndOrdering();
//        indiv.PDFitness();
        int nbIter = 0;
        
        
//        double [] fitnessNS = new double [individualSize];
//        fitnessNS = SPL.getInstance().computeFitnessSums(indiv.getProducts(), SimilarityTechnique.JACCARD_DISTANCE);
//        double[] fitnessValuesNS = new double[individualSize];
//        
//        for (int j = 0; j < fitnessValuesNS.length; j++) {
//            fitnessValuesNS[j] += fitnessNS[j];
//        }
//        System.out.println("初始的累积适应值=" + fitnessValuesNS[individualSize - 1]);
        
        
        while (System.currentTimeMillis() - startTimeMS < timeAllowedMS) {
            Individual newIndiv = new Individual(indiv);
            newIndiv.mutate(mutateType);
            newIndiv.PDfitnessAndOrdering();
//            newIndiv.PDFitness();

            if (newIndiv.getFitness() > indiv.getFitness()) {
                indiv = newIndiv;
            }
            nbIter++;
            
//            System.out.println(nbIter);
//            fitnessNS = new double [individualSize];
//            fitnessNS = SPL.getInstance().computeFitnessSums(indiv.getProducts(), SimilarityTechnique.JACCARD_DISTANCE);
//            fitnessValuesNS = new double[individualSize];
//            
//            for (int j = 0; j < fitnessValuesNS.length; j++) {
//                fitnessValuesNS[j] += fitnessNS[j];
//            }
//            System.out.println("迭代过程累积适应值=" + fitnessValuesNS[individualSize - 1]);
            
        }
        return indiv;
    }
  
    
    public void serializeProducts(String outFile, List<Product> products) {
        try {


            FileOutputStream fileOut = new FileOutputStream(outFile);
            ObjectOutputStream out = new ObjectOutputStream(fileOut);

            out.writeObject(products);
            out.close();
            fileOut.close();

        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}
