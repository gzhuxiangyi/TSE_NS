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
package spl.techniques.ga;

import java.io.FileOutputStream;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

import spl.SPL;
import spl.fm.Product;
import spl.fm.TSet;
import spl.techniques.SimilarityTechnique;

/**
 *
 * @author Christopher Henard
 * 
 * This class represents the search-based approach
 */
public class GA {

    private static Random random;
    private long timeAllowedMS;
    private long TT50;
    private long TT90;
    private long TT95;
    private boolean TT50Flag = false;
    private boolean TT90Flag = false;
    private boolean TT95Flag = false;
    List<Double> runCoverage ; // record coverage during run
    
    public GA(long timeAllowedMS) {
        this.timeAllowedMS = timeAllowedMS;
        this.TT50 = timeAllowedMS;
        this.TT90 = timeAllowedMS;
        this.TT95 = timeAllowedMS;
        random = new Random();
        runCoverage = new ArrayList<Double> ();
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



    public Individual runGA(int individualSize, int populationSize) throws Exception {

//        int a = 1;
//        while (a == 1){
//            Individual indiv = new Individual(SPL.getInstance().getUnpredictableProducts(individualSize));
//            Individual indiv2 = new Individual(SPL.getInstance().getUnpredictableProducts(individualSize));
//            
//            indiv.fitness();
//            indiv2.fitness2();
//            
//            System.out.println("-> "+indiv.getFitness() + " "+indiv2.getFitness());
//            
//            
//            Product p1 = indiv.getProducts().get(0);
//            Product p2 = indiv.getProducts().get(1);
//            long res1=  0, res2=0,t = System.nanoTime();
//            double d = DistancesUtil.getJaccardDistance(p1, p2);
//            res1 = System.nanoTime() - t;
//            boolean[] p1b = productToBits(p1), p2b=productToBits(p2);
//            t = System.nanoTime();
//            
//            d = nSameBits(p1b, p2b);
//            d = 55-(d*(d-1))/2;
//            res2 = System.nanoTime() - t;
//            
//            System.out.println(res1 + " "+res2);
//            Thread.sleep(1000);
//        }
//        
//        
        long startTimeMS = System.currentTimeMillis();
        long lastPrint = 0, printInterval = 30000;


        //init 
        List<Individual> population = new ArrayList<Individual>(populationSize);

        for (int i = 0; i < populationSize; i++) {
            Individual indiv = new Individual(SPL.getInstance().getUnpredictableProducts(individualSize));
            if (!population.contains(indiv)) {
                indiv.fitnessAndOrdering();
                population.add(indiv);
            }
        }

        Collections.sort(population);



        List<Product> prods = population.get(0).getProducts();

        Set<TSet> pairs = new HashSet<TSet>();
//        for (Product p : prods) {
//            productToLi(p);
//            pairs.addAll(p.computeCoveredPairs());
//            //System.out.println(pairs.size());
//        }
//
//        System.out.println(pairs.size());
//        System.out.println(nbPairs(prods));
//        System.exit(0);






        int nbIter = 0;

        //run
        while (System.currentTimeMillis() - startTimeMS < timeAllowedMS) {
            List<Individual> candidates = new ArrayList<Individual>(population);

            Individual offspring;
            double p = random.nextDouble();
            if (p <= 0.8d) {
                offspring = crossover(population.get(0), population.get(1));
            } else {
                p = random.nextDouble();
                if (p <= 0.5d) {
                    offspring = crossover(population.get(0), population.get(population.size() - 1));
                } else {
                    offspring = crossover(population.get(population.size() - 2), population.get(population.size() - 1));
                }
            }
            offspring.fitnessAndOrdering();
            candidates.add(offspring);

            Individual offspringMutated = new Individual(offspring);
            p = random.nextDouble();
            if (p <= 0.8d) {
                offspringMutated.mutate(Individual.MUTATE_WORST);
            } else {
                p = random.nextDouble();
                if (p <= 0.5d) {
                    offspringMutated.mutate(Individual.MUTATE_BEST);
                } else {
                    offspringMutated.mutate(Individual.MUTATE_RANDOM);
                }
            }

            offspringMutated.fitnessAndOrdering();
            candidates.add(offspringMutated);
            Individual randomMutated = population.get(random.nextInt(population.size()));
            p = random.nextDouble();
            if (p <= 0.8d) {
                randomMutated.mutate(Individual.MUTATE_WORST);
            } else {
                p = random.nextDouble();
                if (p <= 0.5d) {
                    randomMutated.mutate(Individual.MUTATE_BEST);
                } else {
                    randomMutated.mutate(Individual.MUTATE_RANDOM);
                }
            }
            randomMutated.fitnessAndOrdering();
            candidates.add(randomMutated);
            Individual rand = new Individual(SPL.getInstance().getUnpredictableProducts(individualSize));
            rand.fitnessAndOrdering();
            candidates.add(rand);
            Collections.sort(candidates);
            population.clear();
            for (int i = 0; i < populationSize; i++) {
                population.add(candidates.get(i));
            }
            nbIter++;

            if (System.currentTimeMillis() - lastPrint > printInterval) {
                System.out.println("Iter: " + nbIter + "; Fitness: " + population.get(0).getFitness() + "; Time: " + (System.currentTimeMillis() - startTimeMS));
                lastPrint = System.currentTimeMillis();
            }
        }
        System.out.println("Iter: " + nbIter + "; Fitness: " + population.get(0).getFitness() + "; Time: " + (System.currentTimeMillis() - startTimeMS));
        return population.get(0);
    }

    
    public long getTT50() {
		return TT50;
	}

	public void setTT50(long tT50) {
		TT50 = tT50;
	}

	public long getTT90() {
		return TT90;
	}

	public void setTT90(long tT90) {
		TT90 = tT90;
	}

	
	public long getTT95() {
		return TT95;
	}

	public void setTT95(long tT95) {
		TT95 = tT95;
	}

	public List<Double> getRunCoverage() {
		return runCoverage;
	}

	public void setRunCoverage(List<Double> runCoverage) {
		this.runCoverage = runCoverage;
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

    public Individual runSimpleGA(int individualSize, int mutateType,String outputDir, String fmFileName, int currentRun) throws Exception {
       
        long sumTimeMS = 0;
        
        long startTimeMS = System.currentTimeMillis();// 开始计时       
        
//        Individual indiv = new Individual(SPL.getInstance().getUnpredictableProducts(individualSize));
        
     // Load products from SAT4JUnpredictableR1 for fair comparison
        String loadPath = "./output/" + "SAT4JUnpredictable/" + fmFileName + "/Samples/" + individualSize + "prods/"+ (timeAllowedMS/1) + "ms/";        
        Individual indiv  = new Individual(SPL.getInstance().loadProductsFromFile(loadPath + "Products." + currentRun));
        
        
        indiv.fitnessAndOrdering();
        int nbIter = individualSize;
        
        sumTimeMS = System.currentTimeMillis() - startTimeMS;        		
        // Record time	
//        timeRecord(indiv,sumTimeMS); 
        
        while (sumTimeMS < timeAllowedMS) {
        	
        	startTimeMS = System.currentTimeMillis();
        	
            Individual newIndiv = new Individual(indiv);
            newIndiv.mutate(mutateType);
            newIndiv.fitnessAndOrdering();
            
            if (newIndiv.getFitness() > indiv.getFitness()) {
                indiv = newIndiv;
            }
            
            nbIter++;
            
            // ----------once more, each time two individuals are considered-------------------
            newIndiv = new Individual(indiv);
            newIndiv.mutate(mutateType);
            newIndiv.fitnessAndOrdering();
            
            if (newIndiv.getFitness() > indiv.getFitness()) {
                indiv = newIndiv;
            }
            
            nbIter++;
            
            // Record time
            sumTimeMS = sumTimeMS + (System.currentTimeMillis() - startTimeMS); //  累加时间 
//            timeRecord(indiv,sumTimeMS);             
            //----------------------------------------------
            
        }
        
        System.out.println("-----------nbIter in Henard's GA------------- " + nbIter);
        System.out.println("-----------sumTimeMS in Henard's GA------------- " + sumTimeMS); 
        
        return indiv;
    }

    public Individual runSimpleGA(int individualSize, int mutateType) throws Exception {
        
        long sumTimeMS = 0;
        
        long startTimeMS = System.currentTimeMillis();// 开始计时       
        
        Individual indiv = new Individual(SPL.getInstance().getUnpredictableProducts(individualSize));
                
        
        indiv.fitnessAndOrdering();
        int nbIter = individualSize;
        
        sumTimeMS = System.currentTimeMillis() - startTimeMS;        		
        // Record time	
//        timeRecord(indiv,sumTimeMS); 
        
        while (sumTimeMS < timeAllowedMS) {
        	
        	startTimeMS = System.currentTimeMillis();
        	
            Individual newIndiv = new Individual(indiv);
            newIndiv.mutate(mutateType);
            newIndiv.fitnessAndOrdering();
            
            if (newIndiv.getFitness() > indiv.getFitness()) {
                indiv = newIndiv;
            }
            
            // ----------once more, each time two individuals are considered-------------------
            newIndiv = new Individual(indiv);
            newIndiv.mutate(mutateType);
            newIndiv.fitnessAndOrdering();
            
            if (newIndiv.getFitness() > indiv.getFitness()) {
                indiv = newIndiv;
            }
            
            nbIter++;
            
            // Record time
            sumTimeMS = sumTimeMS + (System.currentTimeMillis() - startTimeMS); //  累加时间 
//            timeRecord(indiv,sumTimeMS);             
            //----------------------------------------------
            
        }
        
        System.out.println("-----------nbIter in Henard's GA------------- " + nbIter);
        System.out.println("-----------sumTimeMS in Henard's GA------------- " + sumTimeMS); 
        
        return indiv;
    }
 public int runSimpleGA_Convergence(String path,  int numberOfPoints, int individualSize, int mutateType) throws Exception {
        
        long sumTimeMS = 0;    
        
        Individual indiv = new Individual(SPL.getInstance().getUnpredictableProducts(individualSize));
        indiv.fitnessAndOrdering();
        int nbIter = 0;
        
        long startTimeMS = System.currentTimeMillis();// 开始计时,初始化不算时间     
        
        int interval = (int) ((timeAllowedMS - sumTimeMS)/(numberOfPoints - 1));
        
        // Record time	
        int recordTimes = 0;  
    	timeRecord(path,indiv,recordTimes); 
        recordTimes++;   
        
        while (sumTimeMS < timeAllowedMS) {
        	
        	startTimeMS = System.currentTimeMillis();
        	
            Individual newIndiv = new Individual(indiv);
            newIndiv.mutate(mutateType);
            newIndiv.fitnessAndOrdering();
            
            if (newIndiv.getFitness() > indiv.getFitness()) {
                indiv = newIndiv;
            }
            
//            // ----------once more, each time two individuals are considered-------------------
//            newIndiv = new Individual(indiv);
//            newIndiv.mutate(mutateType);
//            newIndiv.fitnessAndOrdering();
//            
//            if (newIndiv.getFitness() > indiv.getFitness()) {
//                indiv = newIndiv;
//            }
            
            nbIter++;
            
            // Record time
            sumTimeMS = sumTimeMS + (System.currentTimeMillis() - startTimeMS); //  累加时间 
            
            if (sumTimeMS >= (recordTimes - 1) * interval && sumTimeMS >= (recordTimes) * interval ) {
            	timeRecord(path,indiv,recordTimes); 
            	recordTimes++;          
            }            
            //----------------------------------------------
            
        }
        
        System.out.println("-----------nbIter in GA------------- " + nbIter);
        System.out.println("-----------sumTimeMS in GA------------- " + sumTimeMS); 
        
        return recordTimes;
    }
 
 /**
  * Record time stones
  * @param indiv
  * @throws Exception 
  */
 public void timeRecord(String path, Individual indiv,int recordTimes) throws Exception {
 	
 	(SPL.getInstance()).writeProductsToFile(path + "Products." + recordTimes, indiv.getProducts());      
    
 }
    public Individual runImprovedGA(int individualSize, int mutateType) throws Exception {
        
        long sumTimeMS = 0;
        
        long startTimeMS = System.currentTimeMillis();// 开始计时        
        Individual indiv = new Individual(SPL.getInstance().getUnpredictableProducts(individualSize));
        indiv.fitness();
        int nbIter = 0;
        
        sumTimeMS = System.currentTimeMillis() - startTimeMS;        		
        // Record time	
//        timeRecord(indiv,sumTimeMS); 
        
        while (sumTimeMS < timeAllowedMS) {
        	
        	startTimeMS = System.currentTimeMillis();
        	
            Individual newIndiv = new Individual(indiv);
            newIndiv.mutate(mutateType);
            newIndiv.fitness();
            
            if (newIndiv.getFitness() > indiv.getFitness()) {
                indiv = newIndiv;
            }
            
            // ----------once more, each time two individuals are considered-------------------
            newIndiv = new Individual(indiv);
            newIndiv.mutate(mutateType);
            newIndiv.fitness();
            
            if (newIndiv.getFitness() > indiv.getFitness()) {
                indiv = newIndiv;
            }
            
            nbIter++;
            
            // Record time
            sumTimeMS = sumTimeMS + (System.currentTimeMillis() - startTimeMS); //  累加时间 
//            timeRecord(indiv,sumTimeMS);             
            //----------------------------------------------
            
        }
        
        System.out.println("-----------nbIter in Improved GA------------- " + nbIter);
        System.out.println("-----------sumTimeMS in Improved GA------------- " + sumTimeMS); 
        
        return indiv;
    }
    
    /**
     * Record time stones
     * @param indiv
     */
    public void timeRecord(Individual indiv,long sumTimeMS) {
    	
        double cov = SPL.getInstance().getCoverage(indiv.getProducts());
        runCoverage.add(cov);
        
        if (cov >= 50 && !TT50Flag) {
        	TT50 = sumTimeMS;
        	TT50Flag = true;
        }
        
        if (cov >= 90 && !TT90Flag) {
        	TT90 = sumTimeMS;
        	TT90Flag = true;
        }
        
        if (cov >= 95 && !TT95Flag) {
        	TT95 = sumTimeMS;
        	TT95Flag = true;
        }
    }
    
    public Individual runSimpleGA2(int mutateType, List<Product> init) throws Exception {
        long startTimeMS = System.currentTimeMillis();
        Individual indiv = new Individual(init);
        System.out.println("first prio...");
        indiv.fitnessAndOrdering();
        System.out.println("Prioritization done in " + (System.currentTimeMillis() - startTimeMS));
        double nbIter = 0;
        int n = 1;
        int a = 1;
        while (a == 1) {
            System.out.println("iter " + nbIter);
            Individual newIndiv = new Individual(indiv);
            newIndiv.mutate(mutateType);
            double fitness = SimilarityTechnique.getJaccardFitnessSum(newIndiv.getProducts());

            if (fitness > indiv.getFitness()) {
                newIndiv.fitnessAndOrdering();
                indiv = newIndiv;
            }

            if (System.currentTimeMillis() - startTimeMS > 10800000) {
                startTimeMS = System.currentTimeMillis();
                System.out.println("Starting serialiazing...");
                serializeProducts("prods_iter" + nbIter + "_3h_" + (n++), indiv.getProducts());
                System.out.println("done");
            }
            nbIter++;
        }
        return indiv;
    }

    public void runSimpleGA3(List<Product> init) throws Exception {

        double nbIter = 0;
        int n = 1;
        int a = 1;
        List<Product> prods = new ArrayList<Product>(init);
        while (a == 1) {
            long t = System.currentTimeMillis();
            System.out.println("Starting iter "+ nbIter +" at "+ t);
            prods.addAll(SPL.getInstance().getUnpredictableProducts(5000));
            System.out.println(prods.size() + " products before prioritiation");
            List<Product> newprods = new SimilarityTechnique(SimilarityTechnique.JACCARD_DISTANCE, SimilarityTechnique.NEAR_OPTIMAL_SEARCH).prioritize2(prods);

            prods = newprods;
            System.out.println(prods.size() + "products after prioritiation");
            System.out.println("Starting serialiazing...");
            serializeProducts("prods_iter" + nbIter, prods);
            System.out.println("done at " + System.currentTimeMillis() + " in "+ (System.currentTimeMillis() - t));

            nbIter++;
        }
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
