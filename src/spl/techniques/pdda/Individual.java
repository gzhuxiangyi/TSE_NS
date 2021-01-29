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
package spl.techniques.pdda;

import java.util.ArrayList;
import java.util.List;

import spl.SPLSnapshoot;
import spl.fm.Product;
import spl.techniques.SimilarityTechnique;

/**
 *
 * @author Christopher Henard
 */
public class Individual implements Comparable<Individual> {

    public static final int MUTATE_WORST = 0;
    public static final int MUTATE_BEST = 1;
    public static final int MUTATE_RANDOM = 2;
    private double fitness;
    private List<Product> products;
    private static SimilarityTechnique st = new SimilarityTechnique(SimilarityTechnique.JACCARD_DISTANCE, SimilarityTechnique.NEAR_OPTIMAL_SEARCH);

    public Individual(Individual other) {
        products = new ArrayList(other.products);
        fitness = -1;
    }

    public Individual(List<Product> products) {
        this.products = products;
    }

    public void fitnessAndOrdering() {
        products = st.prioritize(products);
        fitness = st.getLastFitnessComputed();
    }

    public void PDfitnessAndOrdering() {
        products = st.prioritize(products);
        fitness = st.PD(products);
    }
    
    public void PDFitness() {
        fitness = st.PD(products);
    }
    
    public void fitness() {
        fitness = SimilarityTechnique.getJaccardFitnessSum(products);
    }

    public void fitness2() {
        fitness = SimilarityTechnique.getBinaryDistance(products);
    }

    public double getFitness() {
        return fitness;
    }

    public int getSize() {
        return products.size();
    }

    public List<Product> getProducts() {
        return products;
    }



    public void mutate(int mutateType) throws Exception {

        Product p;
        do {
            p = SPLSnapshoot.getInstance().getUnpredictableProduct();
        } while (products.contains(p));
        switch (mutateType) {
            case MUTATE_WORST:
                products.set(products.size() - 1, p);
                break;
            case MUTATE_BEST:
                products.set(0, p);
                break;
            case MUTATE_RANDOM:
                int ind = (int) (Math.random() * (products.size() - 2)) + 1;
                products.set(ind, p);
                break;
            default:
                ;
        }

    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final Individual other = (Individual) obj;
        if (this.products != other.products && (this.products == null || !this.products.equals(other.products))) {
            return false;
        }
        return true;
    }

    @Override
    public String toString() {
        return "Individual{" + "fitness=" + fitness + ", products=" + products + '}';
    }

    @Override
    public int compareTo(Individual o) {
        double tF = getFitness();
        double oF = o.getFitness();
        return Double.compare(oF, tF);
    }
}
