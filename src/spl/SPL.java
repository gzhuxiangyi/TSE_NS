/* SPL.java
 * 
 * Author:  Yi Xiang <xiangyi@scut.edu.cn> or <gzhuxiang_yi@163.com>
 *  
 * Reference: 
 *  
 * Yi Xiang, Han Huang, Miqing Li, Sizhe Li, and Xiaowei Yang, 
 * Looking For Novelty in Search-based Software Product Line Testing, TSE, 2021
 * 
 * Data: 25/01/2021
 * Copyright (c) 2021 Yi Xiang
 * 
 * Note: This is a free software developed based on the open 
 * source projects PLEDGE <https://github.com/christopherhenard/pledge> 
 * and jMetal<http://jmetal.sourceforge.net>. The copy right of PLEDGE 
 * belongs to  its original author, Christopher Henard, and the copy 
 * right of jMetal belongs to Antonio J. Nebro and Juan J. Durillo. 
 * Nevertheless, this current version can be redistributed and/or 
 * modified under the terms of the GNU General Public License
 * as published by the Free Software Foundation, either version 3 of 
 * the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful, 
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 * 
 */
package spl;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.LineNumberReader;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.OutputStreamWriter;
import java.text.NumberFormat;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.StringTokenizer;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.apache.commons.math3.util.ArithmeticUtils;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.minisat.core.IOrder;
import org.sat4j.minisat.core.Solver;
import org.sat4j.minisat.orders.NegativeLiteralSelectionStrategy;
import org.sat4j.minisat.orders.PositiveLiteralSelectionStrategy;
import org.sat4j.minisat.orders.RandomLiteralSelectionStrategy;
import org.sat4j.minisat.orders.RandomWalkDecorator;
import org.sat4j.minisat.orders.VarOrderHeap;
import org.sat4j.reader.DimacsReader;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.ModelIterator;

import com.beust.jcommander.ParameterException;

import jmetal.encodings.variable.Binary;
import jmetal.qualityIndicator.util.MetricsUtil;
import jmetal.util.PseudoRandom;
import spl.fm.Product;
import spl.fm.TSet;
import spl.techniques.DistancesUtil;
import spl.techniques.SimilarityTechnique;
import spl.techniques.ga.GA;
import spl.techniques.ga.Individual;
import spl.techniques.ns.NoveltySearch1plusN;
import spl.utils.FileUtils;
import splar.core.constraints.CNFClause;
import splar.core.constraints.CNFFormula;
import splar.core.fm.FeatureModel;
import splar.core.fm.XMLFeatureModel;
import splar.plugins.reasoners.sat.sat4j.FMReasoningWithSAT;
import splar.plugins.reasoners.sat.sat4j.ReasoningWithSAT;

public class SPL {

    private static Random randomGenerator = new Random();
    private FeatureModel fm;
    private ReasoningWithSAT reasonerSAT;
    private ISolver solverIterator, dimacsSolver;
    private ProbSATLocalSearch repairSolver;
    
    private  IOrder order = new RandomWalkDecorator(new VarOrderHeap(new RandomLiteralSelectionStrategy()), 1);

    private static SPL instance = null;
    private final int SATtimeout = 1000;
    private final long iteratorTimeout = 150000;
    private boolean dimacs;
    private String dimacsFile;
    private boolean predictable;

    private List<List<Integer>> featureModelConstraints;
    private int nConstraints; // how many constraints
    public int numFeatures; // how many features
    
    public static List<Integer> mandatoryFeaturesIndices;
    public static List<Integer> deadFeaturesIndices;
    public static List<Integer> featureIndicesAllowedFlip;   
	
    public static List<Integer> featuresList = new ArrayList<Integer>();
    public static Map<Integer, String> featuresMap = new HashMap<Integer, String>(); // Map ID with name
     Map<String, Integer> featuresMapRev = new HashMap<String, Integer>(); // Map name with ID
    Set<TSet> validTSets;
 	
    protected SPL() {

    }

    public static void main(String[] args) throws Exception {

  	String [] fms = {
  			// -------------12 FMs, 6S,100 runs------------
				"CounterStrikeSimpleFeatureModel",//24
//				"SPLSSimuelESPnP", //32
//				"DSSample", //41
//				"WebPortal",//43    
//				"Drupal", //48
//				"ElectronicDrum",//52
//				"SmartHomev2.2",//60
//				"VideoPlayer", // 71
//				"Amazon", // 79
//				"ModelTransformation", // 88
//				"CocheEcologico",//94
//				"Printers",//	172	   								
//////							
//////				// -------------13FMs, 30S,100runs------------
//				"E-shop",//	290		    			
//	  			"toybox", //544
//  			"axTLS", //684    			
//				"SPLOT-3CNF-FM-1000-200-0,50-SAT-1",
//				"SPLOT-3CNF-FM-1000-200-0,50-SAT-2",
//				"SPLOT-3CNF-FM-1000-200-0,50-SAT-3",
//				"SPLOT-3CNF-FM-1000-200-0,50-SAT-4",
//				"SPLOT-3CNF-FM-1000-200-0,50-SAT-5",
//				"SPLOT-3CNF-FM-1000-200-0,50-SAT-6",
//				"SPLOT-3CNF-FM-1000-200-0,50-SAT-7",
//				"SPLOT-3CNF-FM-1000-200-0,50-SAT-8",
//				"SPLOT-3CNF-FM-1000-200-0,50-SAT-9",
//				"SPLOT-3CNF-FM-1000-200-0,50-SAT-10",
//  			
//////  			// -------------6FMs, 600S, 100 runs------------	
//  			"ecos-icse11",// 1244 
//  			"freebsd-icse11", // 1396 
//  			"Automotive01", //2513 
//  			"SPLOT-3CNF-FM-5000-1000-0,30-SAT-1",// 5000
//  			"2.6.28.6-icse11", //6888 1
//  			"Automotive02_V3",//18434, YES 

  	};    	
  	
  	boolean dimacs = true;
  	long timeAllowed = 0;     	
  	
  	String outputDir = "./output/";
  	
  	int runs = 1; // How many runs (SET it to 1000 when finding corrections)
  	int nbProds = 100; // How many products returned (50, 100, 500, or any number you want)
  	int t = 3; // t-strength
  	    	    	
  	String fmFile = null;
  	
  	for (int i = 0;i < fms.length;i++) {
  		if (!dimacs) {
  			fmFile = "./all_FM/TSE/" + fms[i] + ".xml"; 
  		} else {
  			fmFile = "./all_FM/TSE/" + fms[i] + ".dimacs"; 
  		}
  			
  		System.out.println(fmFile);
  		SPL.getInstance().initializeModelSolvers(fmFile,  t);
  		
  		if (SPL.getInstance().numFeatures <= 200) {
  			timeAllowed = 6 * 1000; 
  		} else if (SPL.getInstance().numFeatures <= 1000){
  			timeAllowed = 30 * 1000; 
  		} else {
  			timeAllowed = 600 * 1000; 
  		}
  		
//  		timeAllowed = timeAllowed * 2;
  		
  		System.out.println("timeAllowed " + timeAllowed);    		
  		
  		SPL.getInstance().fitnessRelateCoverage(fms[i], outputDir, runs, t, nbProds); // Entry to find correlations between coverage and novelty scores
  		
//  		SPL.getInstance().samplingProductsSAT4JUnpredictable(fmFile, outputDir, runs, nbProds,t,timeAllowed); //Unpredictable   		
//  		SPL.getInstance().findProductsNSR1(fmFile, outputDir, runs, dimacs, t, nbProds, timeAllowed); //NS
//  		SPL.getInstance().findProductsGAR1(fmFile, outputDir, runs, dimacs, t, nbProds, timeAllowed); // GA
//  		SPL.getInstance().samplingDownProductsR1(fmFile, outputDir, runs, t, nbProds, timeAllowed);   // SamplingDown
//  		SPL.getInstance().findProductsGA(fmFile, outputDir, runs, dimacs, t, nbProds, timeAllowed); //Henard's GA
  		
  	}
  	
  } // main
    
    
    public static SPL getInstance() {
        if (instance == null) {
            instance = new SPL();
        }
        return instance;
    }

    private int largestV(int a, int b, double x) {
        int v = a - 1;

        while (getBinomCoeff(v, b) > x) {
            v--;
        }

        return v;
    } // LargestV()

    public double getBinomCoeff(int n, int k) {
        if (k > n) {
            return 0.0;
        } else if (n == k || k == 0) {
            return 1.0;
        } else {
            return ArithmeticUtils.binomialCoefficientDouble(n, k);
        }
    }

    public TSet getITSet(int n, int k, double m, List<Integer> featuresList) {

        double total = getBinomCoeff(n, k);
        if (m >= total) {
            m = total - 1.0;
        }
        TSet tSet = new TSet();
        int a = n;
        int b = k;
        double x = (total - 1.0) - m;  // x is the "dual" of m

        for (int i = 0; i < k; i++) {
            a = largestV(a, b, x);          // largest value v, where v < a and vCb < x
            x = x - getBinomCoeff(a, b);
            b = b - 1;
            tSet.add(featuresList.get(n - 1 - a));
        }

        return tSet;
    }

    public void estimateValidTSets(int t, double sample, Map<Integer, String> featuresMap, List<Integer> featuresList) throws Exception {

        int size = featuresList.size();
        double valids = 0, invalids = 0;
        double total = getBinomCoeff(size, t);
        System.out.println(total + " max total " + t + "-sets");


        for (int j = 0; j < sample; j++) {
            TSet set = getITSet(size, t, Math.floor(Math.random() * total), featuresList);
            if (isValidPair(set, featuresMap, featuresList)) {
                valids++;
            } else {
                invalids++;
            }
        }


        valids = 100 * valids / sample;
        invalids = 100 * invalids / sample;

        System.out.println(valids + "% valids, " + invalids + "% invalids");
        System.out.println((valids / 100.0 * total) + " valids, " + (invalids / 100.0 * total) + " invalids");

    }

    
    public void nCk(int n, int k, Set<TSet> tsets, Map<Integer, String> featuresMap, List<Integer> featuresList) throws Exception {
        int[] a = new int[k];
        nCkH(n, k, 0, a, k, tsets, featuresMap, featuresList);
    }

    public void nCkH(int n, int loopno, int ini, int[] a, int k, Set<TSet> tsets, Map<Integer, String> featuresMap, List<Integer> featuresList) throws Exception {

        if (k == 0) {
            return;
        }

        int i;
        loopno--;
        if (loopno < 0) {
            a[k - 1] = ini - 1;
            TSet p = new TSet();
            for (i = 0; i < k; i++) {
                p.add(featuresList.get(a[i]));
            }
            if (isValidPair(p, featuresMap, featuresList)) {
                tsets.add(p);
            }
            return;

        }
        for (i = ini; i <= n - loopno - 1; i++) {
            a[k - 1 - loopno] = i;
            nCkH(n, loopno, i + 1, a, k, tsets, featuresMap, featuresList);
        }


    }
       
   
    /**
     * The R1 version of NS
     * @param fmFile
     * @param outputDir
     * @param runs
     * @param dimacs
     * @param nbPairs
     * @param t
     * @param nbProds
     * @param timeAllowed
     * @throws Exception
     */
    public void findProductsNSR1(String fmFile, String outputDir, int runs, boolean dimacs, int t, int nbProds, long timeAllowed) throws Exception {

    	 String sNbProds = "" + nbProds;
         String fmFileName = new File(fmFile).getName();     
         
         String NSVariant =  "NS";  //name your algorithm, here is NS        
             
         System.out.println("Start findProductsNS..., Variant name:" + NSVariant);        
                  
         //--------------------------------------Nb----------------------
         int Nb = (nbProds)/2;    // Nb = N/2 is better in most cases    
         //--------------------------------------Nb end----------------------                
         
         double avgCoverage = 0.0;      
         
         double p = 0.1;
         
         // Path to save products
         String path = outputDir + NSVariant + "/" + fmFileName +"/Samples/" + sNbProds + "prods/"+ timeAllowed + "ms/";
         FileUtils.CheckDir(path); 
         
         // Path to save t-wise coverage
         String twisePath = outputDir + NSVariant + "/" + fmFileName +"/" + t + "wise/" + sNbProds + "prods/"+ timeAllowed + "ms/";
         FileUtils.CheckDir(twisePath); 
         
         int [] evaluations = new int [runs]; //          
         
         for (int i = 0; i < runs; i++) {
             System.out.println(NSVariant + "：run " + (i));
             System.out.print("--------Nb------------------- = " + Nb);
             
             List<Product> products = null; 
             double [] runCoverage= new double[nbProds];
             double sumCoverageValues = 0.0;
             
             //Use NS to generate a set of samples                  
             long startTimeMS = System.currentTimeMillis() ;           
             
             NoveltySearch1plusN ns = new NoveltySearch1plusN(nbProds,Nb,0.0,timeAllowed,p);            
             products = ns.runNSR1(outputDir,fmFileName,i,evaluations);
            		 
             long endTimeMS = System.currentTimeMillis() - startTimeMS;
             
             // Write  products and runtime
             writeProductsToFile(path + "Products." + i, products);
             writeDataToFile(path + "RUNTIME." + i, endTimeMS);// write runtime
             writeDataToFile(path + "Evaluations." + i, evaluations[i]);// write average evaluations

 	         //  Compute t-wise coverage 	         
             computeProductsPartialCoverage(products, validTSets);                              
           
             for (int j = 0; j < nbProds; j++) {
                 double cov = products.get(j).getCoverage();
                 sumCoverageValues += cov; //
                 runCoverage[j] = cov;    //
             }
             
             System.out.println(NSVariant + "'s " + t +"-wise coverage = " + sumCoverageValues);    
                   
             avgCoverage = avgCoverage + sumCoverageValues;    
                                  
             writeDataToFile(twisePath + "Coverage." + i, sumCoverageValues);// write coverage
             writeRunCoverageToFile(twisePath + "RunCoverage." + i, runCoverage);// write Run coverage
             
         } // for runs         

         // 
         int avgEvaluations = 0;
         for (int i = 0; i < runs;i++) {
        	 avgEvaluations = avgEvaluations + evaluations[i];
         }
         
         avgCoverage = avgCoverage / runs;   
         avgEvaluations = avgEvaluations/runs;
         
         System.out.println(NSVariant + "'s" + " avgCoverage = " + avgCoverage);
         writeDataToFile(twisePath + "Coverage.avg", avgCoverage);// write average coverage
         writeDataToFile(path + "Evaluations.avg", avgEvaluations);// write average evaluations
    }
    
    /**
     * The R1 version of GA. It is in fact the variant of NS with p=0 and Nb=N
     * @param fmFile
     * @param outputDir
     * @param runs
     * @param dimacs
     * @param nbPairs
     * @param t
     * @param nbProds
     * @param timeAllowed
     * @throws Exception
     */
    public void findProductsGAR1(String fmFile, String outputDir, int runs, boolean dimacs, int t, int nbProds, long timeAllowed) throws Exception {

    	 String sNbProds = "" + nbProds;
         String fmFileName = new File(fmFile).getName();
         
         String NSVariant =  "GA";  // Different variants of NS         
         
         System.out.println("Start findProductsGA..., Variant name:" + NSVariant);
        
         double avgCoverage = 0.0;         
         //SimilarityTechnique st = new SimilarityTechnique(SimilarityTechnique.JACCARD_DISTANCE, SimilarityTechnique.NEAR_OPTIMAL_SEARCH);
       
         double p = 0.0; // Repair probability             
         
         // Path to save products
         String path = outputDir + NSVariant + "/" + fmFileName +"/Samples/" + sNbProds + "prods/"+ timeAllowed + "ms/";
         FileUtils.CheckDir(path); 
         
         // Path to save t-wise coverage
         String twisePath = outputDir + NSVariant + "/" + fmFileName +"/" + t + "wise/" + sNbProds + "prods/"+ timeAllowed + "ms/";
         FileUtils.CheckDir(twisePath); 
         
         int [] evaluations = new int [runs]; // 
         
         for (int i = 0; i < runs; i++) {
             System.out.println(NSVariant + "：run " + (i));
         	
             List<Product> products = null; 
             double [] runCoverage= new double[nbProds];
             double sumCoverageValues = 0.0;
             
                           
             long startTimeMS = System.currentTimeMillis() ;
            
             NoveltySearch1plusN ns = new NoveltySearch1plusN(nbProds,nbProds,0.0,timeAllowed,p);  // Nb = N and p=0 form GA           
             products = ns.runNSR1(outputDir,fmFileName,i,evaluations);
            		 
             long endTimeMS = System.currentTimeMillis() - startTimeMS;
             
             // Write  products and runtime
             writeProductsToFile(path + "Products." + i, products);
             writeDataToFile(path + "RUNTIME." + i, endTimeMS);// write coverage
              	               
             computeProductsPartialCoverage(products, validTSets);                              
           
             for (int j = 0; j < nbProds; j++) {
                 double cov = products.get(j).getCoverage();
                 sumCoverageValues += cov; 
                 runCoverage[j] = cov;    
             }
             
             System.out.println(NSVariant + "'s " + t +"-wise coverage = " + sumCoverageValues);    
                   
             avgCoverage = avgCoverage + sumCoverageValues;    
                                  
             writeDataToFile(twisePath + "Coverage." + i, sumCoverageValues);// write coverage
             writeRunCoverageToFile(twisePath + "RunCoverage." + i, runCoverage);// write Run coverage
         } // for runs         
         
         // 
         int avgEvaluations = 0;
         for (int i = 0; i < runs;i++) {
        	 avgEvaluations = avgEvaluations + evaluations[i];
         }
         
         avgCoverage = avgCoverage / runs;   
         avgEvaluations = avgEvaluations/runs;
         
         System.out.println(NSVariant + "'s" + " avgCoverage = " + avgCoverage);
         writeDataToFile(twisePath + "Coverage.avg", avgCoverage);// write average coverage
         writeDataToFile(path + "Evaluations.avg", avgEvaluations);// write coverage
    }
    
    
   
    /**
     * 
     * @param fmFile
     * @param outputDir
     * @param runs
     * @param dimacs
     * @param nbPairs
     * @param t
     * @param nbProds
     * @param timeAllowed
     * @throws Exception
     */
    public void findProductsNSConvergence(String fmFile, String outputDir, int runs, boolean dimacs, int nbPairs, int t, int nbProds, long timeAllowed) throws Exception {

    	 String sNbProds = "" + nbProds;
         String fmFileName = new File(fmFile).getName();
       
         
         String path = outputDir + "/Convergence/NSprobSAT/data/"+ fmFileName +"/" + sNbProds + "prods/"+ timeAllowed + "ms/";
         FileUtils.CheckDir(path); 
         	             
         int  numberOfPoints = 50;

         if (t == 3) {
	         NoveltySearch1plusN ns = new NoveltySearch1plusN(nbProds,20,0.0,timeAllowed,0.1);             
	         numberOfPoints = ns.runNS_Convergence(path,numberOfPoints,1,Individual.MUTATE_WORST); 
         }  else{
        	 numberOfPoints = getFileNum(path);
         }
         
         System.out.println("numberOfPoints = "  + numberOfPoints);   
         
         String writePath = outputDir + "Convergence/NSprobSAT/" + fmFileName + "/" + t + "wise/" + sNbProds + "prods/"+ timeAllowed + "ms/";
         FileUtils.CheckDir(writePath); 
         
         for (int i = 0; i < numberOfPoints; i++) {
         	
             List<Product> products = null; //
             double [] runCoverage= new double[nbProds];
             double sumCoverageValues = 0.0;
             
             products = loadProductsFromFile(path + "Products." + i);
             
 	         // 计算覆盖率 	       
             computeProductsPartialCoverage(products, validTSets);                              
           
             for (int j = 0; j < nbProds; j++) {
                 double cov = products.get(j).getCoverage();
                 sumCoverageValues += cov; //累积覆盖率
                 runCoverage[j] = cov;    //当前product的覆盖率
             }        
             
//             writeProductsToFile(writePath + "Products." + i, products);
             writeDataToFile(writePath + "Coverage." + i, sumCoverageValues);// write coverage

         } // for runs

    }
           
           
    
    /**
     * 
     * @param fmFile
     * @param outputDir
     * @param runs
     * @param dimacs
     * @param nbPairs
     * @param t
     * @param nbProds
     * @param timeAllowed
     * @throws Exception
     */
    public void findProductsGA(String fmFile, String outputDir, int runs, boolean dimacs, int t, int nbProds, long timeAllowed) throws Exception {


    	 String sNbProds = "" + nbProds;
         String fmFileName = new File(fmFile).getName();

//       System.out.println("Start findProductsNS...");
        
         double avgCoverage = 0.0;
         double avgFitness = 0.0;
         //SimilarityTechnique st = new SimilarityTechnique(SimilarityTechnique.JACCARD_DISTANCE, SimilarityTechnique.NEAR_OPTIMAL_SEARCH);         
                
         
         // Path to save products
         String path = outputDir +  "HenardGA/" + fmFileName +"/Samples/" + sNbProds + "prods/"+ timeAllowed + "ms/";
         FileUtils.CheckDir(path); 
         
         // Path to save t-wise coverage
         String twisePath = outputDir +  "HenardGA/" + fmFileName +"/" + t + "wise/" + sNbProds + "prods/"+ timeAllowed + "ms/";
         FileUtils.CheckDir(twisePath); 
         
         
         for (int i = 0; i < runs; i++) {
//           System.out.println("run " + (i + 1));
         	
             List<Product> products = null; //
             double [] runCoverage= new double[nbProds];
             double sumCoverageValues = 0.0;           
           
             long startTimeMS = System.currentTimeMillis() ;
             GA ga = new GA(timeAllowed);           
             products =  ga.runSimpleGA(nbProds, Individual.MUTATE_WORST,outputDir,fmFileName,i).getProducts();

             long endTimeMS = System.currentTimeMillis() - startTimeMS;
// 	         shuffle(products); // 洗牌
 	 
             computeProductsPartialCoverage(products, validTSets);                              
           
             for (int j = 0; j < nbProds; j++) {
                 double cov = products.get(j).getCoverage();
                 sumCoverageValues += cov; 
                 runCoverage[j] = cov;                }
             
//             System.out.println("GA的累积覆盖率=" + sumCoverageValues);            
             
             /*
              * 计算适应度值
              */
//           products = st.prioritize(products);
//           double fitness = st.getLastFitnessComputed();
//             double fitness = st.PD(products);
//             double fitness = st.noveltyScoreSum(products, 20);
             
//             double[] fitness = null;
//             double sumfitnessValue = 0.0; 
//             
//             fitness = computeFitnessSums(products, SimilarityTechnique.JACCARD_DISTANCE);
//             
//             for (int j = 0; j < fitness.length; j++) {
//             	sumfitnessValue += fitness[j]; // 累积适应度
//             }                         
//             System.out.println("GA的累积适应值=" + fitness);                                            
                   
             avgCoverage = avgCoverage + sumCoverageValues;    
//             avgFitness = avgFitness + fitness;
             
             //Save products           
             writeProductsToFile(path + "Products." + i, products);
             writeDataToFile(path + "RUNTIME." + i, endTimeMS);// write coverage
             
             writeDataToFile(twisePath + "Coverage." + i, sumCoverageValues);// write coverage
//             writeDataToFile(path + "RunCoverage." + i, ga.getRunCoverage());// write coverage
             writeRunCoverageToFile(twisePath + "RunCoverage." + i, runCoverage);// write coverage
//             writeDataToFile(path + "Fitness." + i, fitness);// write PD

//             writeDataToFile(path + "TT50." + i, ga.getTT50());// write TT50
//             writeDataToFile(path + "TT90." + i, ga.getTT90());// write TT90
//             writeDataToFile(path + "TT95." + i, ga.getTT95());// write TT95
             
         } // for runs
         
         avgCoverage = avgCoverage / runs;        
         avgFitness  = avgFitness / runs;        
         System.out.println("GA avgCoverage = " + avgCoverage);
//         System.out.println("GA avgFitness = " + avgFitness);       
         writeDataToFile(twisePath + "Coverage.avg", avgCoverage);// write coverage
//         writeDataToFile(path + "PD.avg", avgFitness);// write coverage
    }
    
    /**
     * Count the number of files in a dir
     * @param path
     * @return
     */
    public int getFileNum(String path) {
    	int num = 0;
		File file = new File(path);
		if (file.exists()) {
			File[] f = file.listFiles();
			for (File fs : f) {
				if (fs.isFile()) {
//					System.out.println(fs.getName());
					num++;
				} 
//				else {
//					num = num + getFileNum(fs.getAbsolutePath());
//				} 
			}
		}
 
		return num;
	}

    /**
     * 
     * @param fmFile
     * @param outputDir
     * @param runs
     * @param dimacs
     * @param nbPairs
     * @param t
     * @param nbProds
     * @param timeAllowed
     * @throws Exception
     */
    public void findProductsGAConvergence(String fmFile, String outputDir, int runs, boolean dimacs, int nbPairs, int t, int nbProds, long timeAllowed) throws Exception {

    	 String sNbProds = "" + nbProds;
         String fmFileName = new File(fmFile).getName();
         
         String path = outputDir + "/Convergence/GA/data/"+ fmFileName +"/" + sNbProds + "prods/"+ timeAllowed + "ms/";
         FileUtils.CheckDir(path); 
         	             
         int  numberOfPoints = 50;
         
         if (t == 3) {
	         GA ga = new GA(timeAllowed);           
	         numberOfPoints = ga.runSimpleGA_Convergence(path,numberOfPoints,nbProds, Individual.MUTATE_WORST);
         }  else{
        	 numberOfPoints = getFileNum(path);
         }
         
         System.out.println("numberOfPoints = "  + numberOfPoints);
         
         String writePath = outputDir + "Convergence/GA/" + fmFileName + "/" + t + "wise/" + sNbProds + "prods/"+ timeAllowed + "ms/";
         FileUtils.CheckDir(writePath); 
         
         for (int i = 0; i < numberOfPoints; i++) {
         	
             List<Product> products = null; //
             double [] runCoverage= new double[nbProds];
             double sumCoverageValues = 0.0;
             
             products = loadProductsFromFile(path + "Products." + i);
             
 	         // 计算覆盖率 	       
             computeProductsPartialCoverage(products, validTSets);                              
           
             for (int j = 0; j < nbProds; j++) {
                 double cov = products.get(j).getCoverage();
                 sumCoverageValues += cov; //累积覆盖率
                 runCoverage[j] = cov;    //当前product的覆盖率
             }        
             
//             writeProductsToFile(writePath + "Products." + i, products);
             writeDataToFile(writePath + "Coverage." + i, sumCoverageValues);// write coverage

         } // for runs
    }
    
    
    /**
     * 
     * @param fmFile
     * @param outputDir
     * @param runs
     * @param dimacs
     * @param nbPairs
     * @param t
     * @param nbProds
     * @param timeAllowed
     * @throws Exception
     */
    public void generateConvergenceMFiles(String fmFile, String outputDir, boolean dimacs, int nbPairs, int nbProds, long timeAllowed) throws Exception {

        NumberFormat nf = NumberFormat.getNumberInstance();
        nf.setMaximumFractionDigits(1); 
        
    	 String sNbProds = "" + nbProds;
         String fmFileName = new File(fmFile).getName();
         MetricsUtil utils = new MetricsUtil();  
         
         String [] algorithms = new String [] {"GA", "NSprobSAT"};
         
         int [] tValues = new int[] {4,5,6};
         
         FileUtils.CheckDir(outputDir + "Convergence/mPlots/");    
        
         String mFileName = "FM_" + fmFileName;
         mFileName =  mFileName.replace('.', '_');
         mFileName = mFileName.replace('-', '_');
                
         String mPath = outputDir + "Convergence/mPlots/"+ mFileName +".m";
         
         // Write header
          FileOutputStream fos   = new FileOutputStream(mPath,false)     ;
 	      OutputStreamWriter osw = new OutputStreamWriter(fos)    ;
 	      BufferedWriter bw      = new BufferedWriter(osw)        ;
 	    
 	            	       	
    	  bw.write("%% Plots for convergence");bw.newLine();	
	      bw.write("clear ");
	      bw.newLine();
	      bw.write("clc ");
	      bw.newLine();
	      
	      bw.write("set(gcf,'Position',[500 200 500 400])"); // ����ͼ����ʾλ��
          bw.newLine();
        
          bw.write("if get(gca,'Position') <= [inf inf 400 400]");
          bw.newLine();
          bw.write("    Size = [3 5 .8 18];");
          bw.newLine();
          bw.write("else");
          bw.newLine();
          bw.write("    Size = [6 3 2 18];");
          bw.newLine();
          bw.write("end");
          bw.newLine();
        
          bw.write("set(gca,'NextPlot','add','Box','on','Fontname','Times New Roman','FontSize',Size(4),'LineWidth',1.3);");
          bw.newLine();
          
    	  int maxNumberOfPoints = 0;
    	  
          for (int i = 0; i < algorithms.length;i++) { 
        	   bw.write(algorithms[i] + "=[");
        	   
        	   String path = outputDir + "/Convergence/" + algorithms[i] + "/data/" + fmFileName +"/" + sNbProds + "prods/"+ timeAllowed + "ms/";
        	   int numberOfPoints = getFileNum(path);
        	   
        	   if (numberOfPoints > maxNumberOfPoints) 
        		   maxNumberOfPoints = numberOfPoints;
        	   
        	   for (int j = 0 ; j < tValues.length; j++) {
        		   int t = tValues[j];
        		   String readPath = outputDir + "Convergence/" + algorithms[i] + "/" + fmFileName + "/" + t + "wise/" + sNbProds + "prods/"+ timeAllowed + "ms/";
        		   
        		  // bw.write(Double.toString(0.0) + " ");
        		   
        		   for (int k = 0; k < numberOfPoints;k++) {
        			    double data =  (utils.readFront(readPath + "/Coverage." + k))[0][0];
        			    if (k <  numberOfPoints - 1) 
        			    	bw.write(Double.toString(data) + " ");
        			    else 
        			    	bw.write(Double.toString(data));
        		   } // for k
        		   
        		   if (j < tValues.length - 1) {
        			   bw.newLine();
        		   } else {
        			   bw.write("];");  bw.newLine();
        		   }
        	   } // for j   
        	   
         } // for i
          
          // 如果数据个数不一致，则复制
          for (int i = 0; i < algorithms.length;i++) {         	  
        	  bw.write("[m" + (i +1) +",n" + (i + 1) +"] = "  + "size(" + algorithms[i] + ");");  bw.newLine();
        	  bw.write("if n" + (i+1) + " < " + maxNumberOfPoints);  bw.newLine();
        	  bw.write("\t" +  algorithms[i] + "(:,n" + (i+1) + "+1:" + maxNumberOfPoints + ") = repmat(" + algorithms[i]+"(:,n" + (i+1) 
        			  + "),1," + maxNumberOfPoints + "-n" + (i+1) +");");  bw.newLine();
        	  bw.write("end");  bw.newLine();        	  
          }
            
          String average = "";
          
//          for (int i = 0; i < algorithms.length;i++) {   
//        	  average = average + "+" + algorithms[i] +"(:,1)";
//          }          
//          average = "("  + average + ")" + "/" +  algorithms.length;    
//          
//          for (int i = 0; i < algorithms.length;i++) {   
//        	  bw.write(algorithms[i] + "(:,1) = " + average +";"); bw.newLine();        
//          }  
          
          bw.newLine();     
          bw.write("set(0,'units','centimeters')");
	      bw.newLine();
	      bw.write("position=[0 0 17 6.5];");
	      bw.newLine();		        
	     
	     String [] property  =new String[]{
				"-ro","-bv","-g>","-md","-k^","-r<","-bs"
		 };
	        
         String x = "1:" +  maxNumberOfPoints + "";
         
         String [] color = new String [] {"b"," r","g","  [0.466,  0.674,  0.188]","y"};
         String [] marks = new String [] {"o"," d"," <","<",">"};
         
         for (int j = 0 ; j < tValues.length; j++) {         
        	        	 
	         for (int i = 0; i < algorithms.length;i++) {	        	 
	        	 String strToWrite = "plot(" + x + ",";
	             if (i%2 == 1) 
//	            	 strToWrite = strToWrite +  algorithms[i] + "(" + (j + 1) + ",:),'-" + marks[j] + "', 'color','" 
//	            			 + color[j] + "','linewidth',0.5,'markersize',5,'markerfacecolor','" + color[j] + "')";
	            	 strToWrite = strToWrite +  algorithms[i] + "(" + (j + 1) + ",:),'-', 'color','" 
        			 + color[j] + "','linewidth',2.5')";
	             else
//	            	 strToWrite = strToWrite +  algorithms[i] + "(" + (j + 1) + ",:),'-." + marks[j] + "', 'color','" 
//	            			 + color[j] + "','linewidth',0.5,'markersize',5)";
	            	 strToWrite = strToWrite +  algorithms[i] + "(" + (j + 1) + ",:),'--', 'color','" 
	            			 + color[j] + "','linewidth',2.5')";
	             
	             bw.write(strToWrite);  bw.newLine();
		         bw.write("hold on");  bw.newLine(); 
	         }	  
	         
         }
         
        bw.write(" tit = title('"+ fmFileName.substring(0, fmFileName.length() - 7) + "');");
        bw.newLine();	
        bw.write("set(tit,'fontsize',20)");
        bw.newLine();
         
        bw.newLine();
        bw.write("xl = xlabel('Time (s)');");
        bw.newLine();
        bw.write("set(xl,'fontsize',20)");
        bw.newLine();
        
        String xlabels = "";
        
        int [] xtick = new int [] {
        		0, (int)(maxNumberOfPoints/4.0),(int)(maxNumberOfPoints/2.0),(int)(maxNumberOfPoints*3/4.0),maxNumberOfPoints
        };
        
        String xticks = "";
        
        for (int i=0;i < xtick.length;i++) {
        	if (i==0) {        		
        		xlabels =  "'" + Double.toString((xtick[i] * ((double)timeAllowed/1000/maxNumberOfPoints))) + "'";
        	}  else {
        		xlabels = xlabels + ",'" + (nf.format(xtick[i] * ((double)timeAllowed/1000/maxNumberOfPoints))) + "'";
        	}
        	
        	if (i==xtick.length - 1) 
        		xticks = xticks + xtick[i] ;
        	else
        		xticks = xticks + xtick[i] + ",";
        		
        }
        
        bw.write("set(gca,'xtick',["  + xticks + "]);");bw.newLine();
        bw.write("set(gca,'xticklabel',{" + xlabels + "})" ); bw.newLine();        

        bw.write("yl = ylabel(' Worse \\leftarrow  Coverage \\rightarrow Better');");
        bw.newLine();
        bw.write("set(yl,'fontsize',20)");
        bw.newLine();
        
        
        String lgd = "lgd = legend(";
        
        for(int t = 0; t < tValues.length - 1;t++) {
        	lgd = lgd + "'" + tValues[t] + "-wise (GA)'" +  ",'" + tValues[t] + "-wise (NS)" + "',";
        }
        
        lgd = lgd + "'" + tValues[tValues.length - 1] + "-wise (GA)'" 
        				+  ",'" + tValues[tValues.length - 1] + "-wise (NS)" + "','location','best');";
        
        bw.write(lgd);
        bw.newLine();
        bw.write("set(lgd,'fontsize',13)");
        bw.newLine();
        bw.write("set(lgd,'box','off')");bw.newLine();
        
        
         bw.close();         
         System.out.println("Generate m script for "  + fmFileName + " done!");
    }
    
    
    /**
     * 
     * @param fmFile
     * @param outputDir
     * @param runs
     * @param dimacs
     * @param nbPairs
     * @param t
     * @param nbProds
     * @param timeAllowed
     * @throws Exception
     */
    public void generatePrioritisationConvergenceMFiles(String fmFile, String outputDir, boolean dimacs, int nbPairs, int t,int nbProds, long timeAllowed) throws Exception {

        NumberFormat nf = NumberFormat.getNumberInstance();
        nf.setMaximumFractionDigits(1); 
        
    	 String sNbProds = "" + nbProds;
         String fmFileName = new File(fmFile).getName();
         MetricsUtil utils = new MetricsUtil();  
         
         String [] algorithms = new String [] {"NearOptimal", "GA","SamplingDown","SAT4JUnpredictable"}; //NearOptimal是NS+近似最优排序"NSprobSAT",
         
         //int [] tValues = new int[] {2};
         
         FileUtils.CheckDir(outputDir + "Prioritisation/mPlots/" + t + "Wise/" );    
        
         String mFileName = "FM_" + fmFileName;
         mFileName =  mFileName.replace('.', '_');
         mFileName = mFileName.replace('-', '_');
         mFileName = mFileName.replace(',', '_');
         
         String mPath = outputDir + "Prioritisation/mPlots/"+ t + "Wise/"  + mFileName + ".m";
         
         // Write header
          FileOutputStream fos   = new FileOutputStream(mPath,false)     ;
 	      OutputStreamWriter osw = new OutputStreamWriter(fos)    ;
 	      BufferedWriter bw      = new BufferedWriter(osw)        ;
 	    
 	            	       	
    	  bw.write("%% Plots for convergence");bw.newLine();	
	      bw.write("clear ");
	      bw.newLine();
	      bw.write("clc ");
	      bw.newLine();
	      
	      bw.write("set(gcf,'Position',[500 200 550 550])"); // ����ͼ����ʾλ��
          bw.newLine();
        
          bw.write("if get(gca,'Position') <= [inf inf 400 400]");
          bw.newLine();
          bw.write("    Size = [3 5 .8 18];");
          bw.newLine();
          bw.write("else");
          bw.newLine();
          bw.write("    Size = [6 3 2 18];");
          bw.newLine();
          bw.write("end");
          bw.newLine();
        
          bw.write("set(gca,'NextPlot','add','Box','on','Fontname','Times New Roman','FontSize',Size(4),'LineWidth',1.3);");
          bw.newLine();
              	  
          for (int i = 0; i < algorithms.length;i++) { 
        	   bw.write(algorithms[i] + "=[");        	   
         	   
//        	   for (int j = 0 ; j < tValues.length; j++) {
//        		   int t = tValues[j];
        		   String readPath = outputDir + "Prioritisation/" + algorithms[i] + "/" + fmFileName + "/" + t + "wise/" + sNbProds + "prods/"+ timeAllowed + "ms/";
        		   double[][] data  = utils.readFront(readPath + "/Coverage");
        		  // bw.write(Double.toString(0.0) + " ");
        		   
        		   for (int k = 0; k < nbProds + 1;k++) {
        			    double val =  data[k][0];
        			    if (k < nbProds) 
        			    	bw.write(Double.toString(val) + " ");
        			    else 
        			    	bw.write(Double.toString(val));
        		   } // for k
        		   
//        		   if (j < tValues.length - 1) {
//        			   bw.newLine();
//        		   } else {
        			   bw.write("];");  bw.newLine();
//        		   }
//        	   } // for j   
        	   
         } // for i
          
          // 如果数据个数不一致，则复制
          for (int i = 0; i < algorithms.length;i++) {         	  
        	  bw.write("[m" + (i +1) +",n" + (i + 1) +"] = "  + "size(" + algorithms[i] + ");");  bw.newLine();
        	  bw.write("if n" + (i+1) + " < " + (nbProds + 1));  bw.newLine();
        	  bw.write("\t" +  algorithms[i] + "(:,n" + (i+1) + "+1:" + (nbProds + 1) + ") = repmat(" + algorithms[i]+"(:,n" + (i+1) 
        			  + "),1," + (nbProds + 1) + "-n" + (i+1) +");");  bw.newLine();
        	  bw.write("end");  bw.newLine();        	  
          }
            
          String average = "";
          
//          for (int i = 0; i < algorithms.length;i++) {   
//        	  average = average + "+" + algorithms[i] +"(:,1)";
//          }          
//          average = "("  + average + ")" + "/" +  algorithms.length;    
//          
//          for (int i = 0; i < algorithms.length;i++) {   
//        	  bw.write(algorithms[i] + "(:,1) = " + average +";"); bw.newLine();        
//          }  
          
          bw.newLine();     
          bw.write("set(0,'units','centimeters')");
	      bw.newLine();
	      bw.write("position=[0 0 17 6.5];");
	      bw.newLine();		        
	     
	     String [] property  =new String[]{
				"-ro","-bv","-g>","-md","-k^","-r<","-bs"
		 };
	        
         String x = "1:2:" +  (nbProds + 1) + "";
         
         String [] color = new String [] {"r","b","k"," g","m"};
         String [] marks = new String [] {"o"," d"," <","v",">"};
         
         for (int j = 0 ; j < 1; j++) {         
        	        	 
	         for (int i = 0; i < algorithms.length;i++) {	        	 
	        	 String strToWrite = "plot(" + x + ",";
//	             if (i%2 == 1) 
	            	 strToWrite = strToWrite +  algorithms[i] + "(" + x + "),'-" + marks[i] + "', 'color','" 
	            			 + color[i] + "','linewidth',1,'markersize',3,'markerfacecolor','" + color[i] + "')";
//	            	 strToWrite = strToWrite +  algorithms[i] + "(" + (j + 1) + ",:),'-', 'color','" 
//        			 + color[j] + "','linewidth',2.5')";
//	             else
//	            	 strToWrite = strToWrite +  algorithms[i] + "(" + (j + 1) + ",:),'-." + marks[j] + "', 'color','" 
//	            			 + color[j] + "','linewidth',0.5,'markersize',5)";
//	            	 strToWrite = strToWrite +  algorithms[i] + "(" + (j + 1) + ",:),'--', 'color','" 
//	            			 + color[j] + "','linewidth',2.5')";
	             
	             bw.write(strToWrite);  bw.newLine();
		         bw.write("hold on");  bw.newLine(); 
	         }	  
	         
         }
         
        bw.write(" tit = title('"+ fmFileName.substring(0, fmFileName.length() - 7) + "');");
        bw.newLine();	
        bw.write("set(tit,'fontsize',20)");
        bw.newLine();
         
        bw.write("xlim([0," + (nbProds + 1) + "]);"); bw.newLine();
        
        bw.newLine();
        bw.write("xl = xlabel('Product configurations used');");
        bw.newLine();
        bw.write("set(xl,'fontsize',20)");
        bw.newLine();
        
        String xlabels = "";
        
        int [] xtick = new int [] {
        		0, (int)((nbProds + 1)/4.0),(int)((nbProds + 1)/2.0),(int)((nbProds + 1)*3/4.0),(nbProds + 1)
        };
        
        String xticks = "";
        
        for (int i=0;i < xtick.length;i++) {
        	if (i==0) {        		
        		xlabels =  "'" + Double.toString(xtick[i]/(double)(nbProds + 1) * 100) + "%'";
        	}  else {
        		xlabels = xlabels + ",'" + (nf.format(xtick[i]/(double)(nbProds + 1)* 100.0)) + "%'";
        	}
        	
        	if (i==xtick.length - 1) 
        		xticks = xticks + xtick[i] ;
        	else
        		xticks = xticks + xtick[i] + ",";        		
        }
        
        xlabels = "'0%','25%','50%','75%','100%'";
        
        bw.write("set(gca,'xtick',["  + xticks + "]);");bw.newLine();
        bw.write("set(gca,'xticklabel',{" + xlabels + "})" ); bw.newLine();        

        bw.write("yl = ylabel(' " + t + "-wise coverage (%)');");
        bw.newLine();
        bw.write("set(yl,'fontsize',20)");
        bw.newLine();
        
        
        String lgd = "lgd = legend(";
        
//        for(int t = 0; t < tValues.length - 1;t++) {
//        	lgd = lgd + "'" + tValues[t] + "-wise (GA)'" +  ",'" + tValues[t] + "-wise (NS)" + "',";
//        }
//        
//        lgd = lgd + "'" + tValues[tValues.length - 1] + "-wise (GA)'" 
//        				+  ",'" + tValues[tValues.length - 1] + "-wise (NS)" + "','location','best');";
        
        for (int i = 0; i < algorithms.length; i++) {
        	if (i < algorithms.length - 1) 
        		lgd = lgd +  "'" + algorithms[i] + "'," ;
        	else 
        		lgd = lgd +  "'" + algorithms[i] +  "','location','southeast');";
        }
        
        bw.write(lgd);
        bw.newLine();
        bw.write("set(lgd,'fontsize',13)");
        bw.newLine();
        bw.write("set(lgd,'box','off')");bw.newLine();
        
        
         bw.close();         
         System.out.println("Generate m script for "  + fmFileName + " done!");
    }
    
    
    /**
     * 
     * @param products
     * @return
     */
    public double getCoverage(List <Product> products) {
    	
    	computeProductsPartialCoverage(products, validTSets);                              
        double coverage = 0.0;
        
        for (int j = 0; j < products.size(); j++) {
            double cov = products.get(j).getCoverage();
            coverage += cov; //累积覆盖率           
        }
        return coverage;
    }
       
   
    
    public void computeProductsGA(String fmFile, String outputDir, int runs, boolean dimacs, int nbPairs, int t, int nbProds, long timeAllowed) throws Exception {


        File output = new File(outputDir);
        if (!output.isDirectory()) {
            throw new ParameterException("Output directory specified is incorrect");
        }
        if (runs < 1) {
            throw new ParameterException("Number of runs specified incorrect");
        }

        if (!outputDir.endsWith("/")) {
            outputDir += "/";
        }

        if (!new File(fmFile).exists()) {
            throw new ParameterException("The specified FM file does not exist");
        }


        if (nbProds < 0) {
            throw new ParameterException("Negative nbRuns");
        }


        this.predictable = false;
        this.dimacs = dimacs;
        this.dimacsFile = fmFile;
        
        // 初始化求解器
        if (!dimacs) {
            fm = loadFeatureModel(fmFile);
            fm.loadModel();
            reasonerSAT = new FMReasoningWithSAT("MiniSAT", fm, SATtimeout);
            reasonerSAT.init();
        } else {
            dimacsSolver = SolverFactory.instance().createSolverByName("MiniSAT");
            dimacsSolver.setTimeout(SATtimeout);

            DimacsReader dr = new DimacsReader(dimacsSolver);
            dr.parseInstance(new FileReader(fmFile));
        }

        // 
        List<Integer> featuresList = new ArrayList<Integer>();
        Map<Integer, String> featuresMap = new HashMap<Integer, String>(); // ID 与name关联
        Map<String, Integer> featuresMapRev = new HashMap<String, Integer>(); // name 与ID关联

        //处理feature，将其ID与name相互关联，建立索引
        if (!dimacs) {
            computeFeatures(reasonerSAT, featuresMap, featuresMapRev, featuresList, false, null);
        } else {
            computeFeatures(null, featuresMap, featuresMapRev, featuresList, true, fmFile);
        }


        System.out.println(featuresList.size() + " features"); // 加入了负特征,故个数是真实的两倍

        System.out.println("Sampling " + nbPairs + " valid " + t + "-sets...");
        Set<TSet> validTSets = computeNRandValidTSets(featuresMap, featuresList, nbPairs, t);

      
        String validPairsFile = fmFile+".validpairs";
    	System.out.println(validPairsFile);
    	
//    	  Set<TSet> validTSets;
//        if (validPairsFile != null) {
//        	validTSets = loadPairs(validPairsFile);    
//        	System.out.println("Number of validTSets " + validTSets.size());
//        } else {
//        	validTSets = computeValidPairs(featuresMap, featuresList, null, false, null, 1, 1);
//        }   
    	
      
        GA ga = new GA(timeAllowed);
        String sNbProds = "" + nbProds;

        String fmFileName = new File(fmFile).getName();
        System.out.println("Starting the runs...");
        
        double avgCoverage = 0.0;
        
        for (int i = 0; i < runs; i++) {
        	
//            System.out.println("run " + (i + 1));
            double[] coverageValuesSimpleGA = new double[nbProds];
            double[] fitnessValuesSimpleGA = new double[nbProds];


            // 获得迭代器
            if (!dimacs) {
                reasonerSAT.init();
                if (!predictable) {
                	((Solver) reasonerSAT.getSolver()).setOrder(order);
                }
                solverIterator = new ModelIterator(reasonerSAT.getSolver());
//                solverIterator = reasonerSAT.getSolver();
                solverIterator.setTimeoutMs(iteratorTimeout);
            } else {
            	if (!predictable) {
            		((Solver) dimacsSolver).setOrder(order);
            	}
                solverIterator = new ModelIterator(dimacsSolver);
//                solverIterator =  dimacsSolver;
                solverIterator.setTimeoutMs(iteratorTimeout);
            }
                       
//            System.out.println("Start SimpleGA...");
            List<Product> gaSimpleRes = ga.runSimpleGA(nbProds, Individual.MUTATE_WORST).getProducts();
//            System.out.println("End SimpleGA, coverage...");

            double[] runCoverageGA = null;
            double[] fitnessSimpleGA = null;

            computeProductsPartialCoverage(gaSimpleRes, validTSets);
//            computeProductsCoverage(gaSimpleRes, validTSets);
                        
            runCoverageGA = new double[coverageValuesSimpleGA.length];
            double sumCoverageValuesGA= 0.0;
            
            for (int j = 0; j < nbProds; j++) {
                double cov = gaSimpleRes.get(j).getCoverage();
                sumCoverageValuesGA += cov;
                runCoverageGA[j] = cov;
            }
            
//            System.out.println("GA的累积覆盖率=" + sumCoverageValuesGA);
            
            avgCoverage = avgCoverage + sumCoverageValuesGA;
             
            fitnessSimpleGA = computeFitnessSums(gaSimpleRes, SimilarityTechnique.JACCARD_DISTANCE);
            for (int j = 0; j < fitnessValuesSimpleGA.length; j++) {
                fitnessValuesSimpleGA[j] += fitnessSimpleGA[j];
            }

//            System.out.println("GA的累积适应值=" + fitnessValuesSimpleGA[nbProds - 1]);
                        
            
            //run values
            writeCoverageAndFitnessValuesToFile(outputDir + fmFileName + "_SimpleGAProducts-" + t + "wise-" + sNbProds + "prods-" + timeAllowed + "ms-run" + (i + 1) + ".dat", runCoverageGA, fitnessSimpleGA);

        }
        
        avgCoverage = avgCoverage/runs;
        System.out.println("GA avgCoverage = " + avgCoverage);

    }
    
    public void computeProductsUnpredictable(String fmFile, String outputDir, int runs, boolean dimacs, int nbPairs, int t, int nbProds, long timeAllowed) throws Exception {


        File output = new File(outputDir);
        if (!output.isDirectory()) {
            throw new ParameterException("Output directory specified is incorrect");
        }
        if (runs < 1) {
            throw new ParameterException("Number of runs specified incorrect");
        }

        if (!outputDir.endsWith("/")) {
            outputDir += "/";
        }

        if (!new File(fmFile).exists()) {
            throw new ParameterException("The specified FM file does not exist");
        }


        if (nbProds < 0) {
            throw new ParameterException("Negative nbRuns");
        }


        this.predictable = false;
        this.dimacs = dimacs;
        this.dimacsFile = fmFile;
        
        // 初始化求解器
        if (!dimacs) {
            fm = loadFeatureModel(fmFile);
            fm.loadModel();
            reasonerSAT = new FMReasoningWithSAT("MiniSAT", fm, SATtimeout);
            reasonerSAT.init();
        } else {
            dimacsSolver = SolverFactory.instance().createSolverByName("MiniSAT");
            dimacsSolver.setTimeout(SATtimeout);

            DimacsReader dr = new DimacsReader(dimacsSolver);
            dr.parseInstance(new FileReader(fmFile));
        }

        // 
        List<Integer> featuresList = new ArrayList<Integer>();
        Map<Integer, String> featuresMap = new HashMap<Integer, String>(); // ID 与name关联
        Map<String, Integer> featuresMapRev = new HashMap<String, Integer>(); // name 与ID关联

        //处理feature，将其ID与name相互关联，建立索引
        if (!dimacs) {
            computeFeatures(reasonerSAT, featuresMap, featuresMapRev, featuresList, false, null);
            computeConstraints(reasonerSAT, false, null);
        } else {
            computeFeatures(null, featuresMap, featuresMapRev, featuresList, true, fmFile);
            computeConstraints(null, true, fmFile);
        }
        
        numFeatures = featuresList.size()/2;

//        System.out.println(featuresList.size() + " features"); // 加入了负特征,故个数是真实的两倍

//        System.out.println("Sampling " + nbPairs + " valid " + t + "-sets...");
        Set<TSet> validTSets = computeNRandValidTSets(featuresMap, featuresList, nbPairs, t);

      
        String validPairsFile = fmFile+".validpairs";
//    	System.out.println(validPairsFile);
    	
//    	  Set<TSet> validTSets;
//        if (validPairsFile != null) {
//        	validTSets = loadPairs(validPairsFile);    
//        	System.out.println("Number of validTSets " + validTSets.size());
//        } else {
//        	validTSets = computeValidPairs(featuresMap, featuresList, null, false, null, 1, 1);
//        }
                

        String sNbProds = "" + nbProds;
        String fmFileName = new File(fmFile).getName();
        
//        System.out.println("Starting the runs...");
        
        double avgCoverage = 0.0;
                
        for (int i = 0; i < runs; i++) {
        	
            double[] coverageValuesUnpredictable = new double[nbProds];
            double[] fitnessValuesUnpredictable = new double[nbProds];
            
            // 获得迭代器
            if (!dimacs) {
                reasonerSAT.init();
                if (!predictable) {
                	((Solver) reasonerSAT.getSolver()).setOrder(order);
                }
//                solverIterator = new ModelIterator(reasonerSAT.getSolver());
                solverIterator = reasonerSAT.getSolver();
                solverIterator.setTimeoutMs(iteratorTimeout);
            } else {
            	if (!predictable) {
            		((Solver) dimacsSolver).setOrder(order);
            	}
//                solverIterator = new ModelIterator(dimacsSolver);
                solverIterator =  dimacsSolver;
                solverIterator.setTimeoutMs(iteratorTimeout);
            }
                        
//            System.out.println("run " + (i + 1));

            double[] runCoverageUnpredictable = null;
            double[] fitnessUnpredictable = null;
            List<Product> unpredictableProducts = null;
            List<Product> simOptiPrioritizedUnpredictable = null;

            //-----------------------unpredictable products----------------------------------
//            System.out.println("Start Unpredictable...");
            unpredictableProducts = getUnpredictableProducts(nbProds); //生成一组随机解
            shuffle(unpredictableProducts);
//            System.out.println("End Unpredictable, coverage...");

            computeProductsPartialCoverage(unpredictableProducts, validTSets);
            runCoverageUnpredictable = new double[coverageValuesUnpredictable.length];

            double sumCoverageValuesUnpredictable = 0.0;
            for (int j = 0; j < nbProds; j++) {
                double cov = unpredictableProducts.get(j).getCoverage();
                sumCoverageValuesUnpredictable += cov; //累积覆盖率
                runCoverageUnpredictable[j] = cov;    //当前product的覆盖率
            }

//            System.out.println("Unpredictable的累积覆盖率=" + sumCoverageValuesUnpredictable);
            avgCoverage = avgCoverage + sumCoverageValuesUnpredictable;
            
            fitnessUnpredictable = computeFitnessSums(unpredictableProducts, SimilarityTechnique.JACCARD_DISTANCE);
            for (int j = 0; j < fitnessUnpredictable.length; j++) {
                fitnessValuesUnpredictable[j] += fitnessUnpredictable[j]; // 累积适应度
            }
            
//            System.out.println("Unpredictable的累积适应值=" + fitnessValuesUnpredictable[nbProds - 1]);                                            
            
            //run values
            writeCoverageAndFitnessValuesToFile(outputDir + fmFileName + "_UnpredictableProducts-" + t + "wise-" + sNbProds + "prods-" + timeAllowed + "ms-run" + (i + 1) + ".dat", runCoverageUnpredictable, fitnessUnpredictable);
           
            //save products
//            writeProductsToFile(outputDir + fmFileName + "_GA-UnpredictableProducts-" + t + "wise-" + sNbProds + "prods-" + timeAllowed + "ms-" + "run" + (i + 1) + ".products.csv", unpredictableProducts, featuresMap, featuresList);
//            writeProductsToFile(outputDir + fmFileName + "_GA-SimpleGAProducts-" + t + "wise-" + sNbProds + "prods-" + timeAllowed + "ms-" + "run" + (i + 1) + ".products.csv", gaSimpleRes, featuresMap, featuresList);

//            serializeProducts(outputDir + fmFileName + "_GA-UnpredictableProducts-" + t + "wise-" + sNbProds + "prods-" + timeAllowed + "ms-" + "run" + (i + 1) + ".products.dat", unpredictableProducts);
//            serializeProducts(outputDir + fmFileName + "_GA-SimpleGAProducts-" + t + "wise-" + sNbProds + "prods-" + timeAllowed + "ms-" + "run" + (i + 1) + ".products.dat", gaSimpleRes);

        }
        
        avgCoverage = avgCoverage / runs;        
        System.out.println("Unpredictable avgCoverage = " + avgCoverage);

    }
    
       
    
    
    public void generateProductsWithGA(String fmFile, String splcatFile, String outputDir, int nbProds, /*int popSize,*/ int runs, long timeAllowed, String validPairsFile, boolean dimacs, boolean noCoverage, boolean onlyGA) throws Exception {

        File output = new File(outputDir);
        if (!output.isDirectory()) {
            throw new ParameterException("Output directory specified is incorrect");
        }
        if (runs < 1) {
            throw new ParameterException("Number of runs specified incorrect");
        }

        if (!outputDir.endsWith("/")) {
            outputDir += "/";
        }

        if (!new File(fmFile).exists()) {
            throw new ParameterException("The specified FM file does not exist");
        }

        if (validPairsFile != null && !new File(validPairsFile).exists()) {
            throw new ParameterException("The specified valid pairs file does not exist");
        }

        if (nbProds < 0 && splcatFile == null) {
            throw new ParameterException("If -nbRuns < 0 then the csv file is mandatory!");
        }

        File splcatCSV = null;
        if (splcatFile != null) {
            splcatCSV = new File(splcatFile);
            if (!splcatCSV.exists()) {
                throw new ParameterException("The specified SPLCAT file does not exist");
            }
        }

        this.predictable = false;
        this.dimacs = dimacs;
        this.dimacsFile = fmFile;
        if (!dimacs) {
            fm = loadFeatureModel(fmFile);
            fm.loadModel();
            reasonerSAT = new FMReasoningWithSAT("MiniSAT", fm, SATtimeout);
            reasonerSAT.init();
        } else {
            dimacsSolver = SolverFactory.instance().createSolverByName("MiniSAT");
            dimacsSolver.setTimeout(SATtimeout);

            DimacsReader dr = new DimacsReader(dimacsSolver);
            dr.parseInstance(new FileReader(fmFile));
        }




        List<Integer> featuresList = new ArrayList<Integer>();
        Map<Integer, String> featuresMap = new HashMap<Integer, String>();
        Map<String, Integer> featuresMapRev = new HashMap<String, Integer>();

        if (!dimacs) {
            computeFeatures(reasonerSAT, featuresMap, featuresMapRev, featuresList, false, null);
        } else {
            computeFeatures(null, featuresMap, featuresMapRev, featuresList, true, fmFile);
        }


        System.out.println(featuresMapRev.size() + " features");

        Set<TSet> validPairs = null;

        if (!noCoverage) {

            if (validPairsFile != null) {
                System.out.println("Loading valid pairs from the file...");
                validPairs = loadPairs(validPairsFile);
            }
        }

        String sNbProds = "" + nbProds;

        if (nbProds < 0) {

            List<Product> splcatProducts = loadProductsFromCSVFile(splcatCSV, featuresMapRev);
            nbProds = splcatProducts.size();
            sNbProds = "SPLCAT";
            if (!noCoverage) {
                if (validPairs == null) {
                    validPairs = computePairsCoveredByProducts(splcatProducts);
                }
            }
        }

        if (!noCoverage) {
            if (validPairs == null) {
                if (!dimacs) {
                    validPairs = computeValidPairs(featuresMap, featuresList, null, false, null, 1, 1);
                } else {
                    computeValidPairs(featuresMap, featuresList, (fmFile + ".validpairs"), true, dimacsSolver, 1, 1);
                }
            }

            System.out.println(validPairs.size() + " valid pairs.");
        }
        System.out.println(nbProds + " products to generate, " + runs + " runs");


        this.estimateValidTSets(6, 1000, featuresMap, featuresList);

        System.exit(0);


        double[] coverageValuesUnpredictable = new double[nbProds];
        double[] fitnessValuesUnpredictable = new double[nbProds];
        double[] coverageValuesUnpredictablePrioritized = new double[nbProds];
        double[] fitnessValuesUnpredictablePrioritized = new double[nbProds];
        double[] coverageValuesSimpleGA = new double[nbProds];
        double[] fitnessValuesSimpleGA = new double[nbProds];


        if (!dimacs) {
            reasonerSAT.init();
            ((Solver) reasonerSAT.getSolver()).setOrder(order);
            solverIterator = new ModelIterator(reasonerSAT.getSolver());
            solverIterator.setTimeoutMs(iteratorTimeout);
        } else {
            ((Solver) dimacsSolver).setOrder(order);
            solverIterator = new ModelIterator(dimacsSolver);
            solverIterator.setTimeoutMs(iteratorTimeout);
        }

        GA ga = new GA(timeAllowed);
        String fmFileName = new File(fmFile).getName();
        System.out.println("Starting the runs...");
        for (int i = 0; i < runs; i++) {
            System.out.println("run " + (i + 1));


            double[] runCoverageUnpredictable = null;
            double[] fitnessUnpredictable = null;
            double[] runCoverageUnpredictablePrioritized = null;
            double[] fitnessUnpredictablePrioritized = null;
            List<Product> unpredictableProducts = null;
            List<Product> simOptiPrioritizedUnpredictable = null;
            if (!onlyGA) {

                //unpredictable products
                System.out.println("Unpredictable...");
                unpredictableProducts = getUnpredictableProducts(nbProds);

                if (!noCoverage) {
                    System.out.println("done, coverage...");
                } else {
                    System.out.println("done.");
                }
                shuffle(unpredictableProducts);



                if (!noCoverage) {

                    computeProductsCoverage(unpredictableProducts, validPairs);
                    runCoverageUnpredictable = new double[coverageValuesUnpredictable.length];

                    for (int j = 0; j < nbProds; j++) {
                        double cov = unpredictableProducts.get(j).getCoverage();
                        coverageValuesUnpredictable[j] += cov;
                        runCoverageUnpredictable[j] = cov;
                    }

                    fitnessUnpredictable = computeFitnessSums(unpredictableProducts, SimilarityTechnique.JACCARD_DISTANCE);
                    for (int j = 0; j < fitnessUnpredictable.length; j++) {
                        fitnessValuesUnpredictable[j] += fitnessUnpredictable[j];

                    }
                }

                //unpredictable prioritized
                System.out.println("unpredictable prioritized...");
                simOptiPrioritizedUnpredictable = new SimilarityTechnique(SimilarityTechnique.JACCARD_DISTANCE, SimilarityTechnique.NEAR_OPTIMAL_SEARCH).prioritize(unpredictableProducts);
                if (!noCoverage) {
                    System.out.println("done, coverage...");
                } else {
                    System.out.println("done.");
                }


                if (!noCoverage) {

                    computeProductsCoverage(simOptiPrioritizedUnpredictable, validPairs);
                    runCoverageUnpredictablePrioritized = new double[coverageValuesUnpredictablePrioritized.length];
                    for (int j = 0; j < nbProds; j++) {
                        double cov = simOptiPrioritizedUnpredictable.get(j).getCoverage();
                        coverageValuesUnpredictablePrioritized[j] += cov;
                        runCoverageUnpredictablePrioritized[j] = cov;
                    }
                    fitnessUnpredictablePrioritized = computeFitnessSums(simOptiPrioritizedUnpredictable, SimilarityTechnique.JACCARD_DISTANCE);
                    for (int j = 0; j < fitnessValuesUnpredictablePrioritized.length; j++) {
                        fitnessValuesUnpredictablePrioritized[j] += fitnessUnpredictablePrioritized[j];

                    }
                }

            }

            System.out.println("Simple GA...");


//            int a = 1;
//            while (a < 5) {
//                Product p = getUnpredictableProduct();
//                //if (p.getSelectedNumber() < 2000)
//                    System.out.println(p.getSelectedNumber());
//                Thread.sleep(100);
//            }

//            System.out.println(isDimacsValid(featuresMap));
//            System.exit(0);


            List<Product> gaSimpleRes = ga.runSimpleGA(nbProds, Individual.MUTATE_WORST).getProducts();
            //List<Product> gaSimpleRes = ga.runGA(nbProds, 5).getProducts();
//            int a = 1;
//
//            List<Product> gaSimpleRes = null;
//            int nbsuc = 0, nbfail = 0;
//            List<Product> smallProducts = new ArrayList<Product>();
//            while (a < 5) {
////                gaSimpleRes = ga.runSimpleGA(nbProds, Individual.MUTATE_WORST).getProducts();
//                //List<Product> gaSimpleRes = ga.runGA(nbProds, 5).getProducts();
//
////                System.out.println("succ: " + nbsuc + " fails:" + nbfail);
//                try {
//
//                    Product p = getUnpredictableProduct();
//                    if (p.getSelectedNumber() < 300) {
//                        System.out.println(p.getSelectedNumber());
//                        if (!smallProducts.contains(p)) {
//                            smallProducts.add(p);
//                            if (smallProducts.size() >= 15){
//                                writeProductsToFile("15prods.csv", smallProducts, featuresMap, featuresList);
//                                System.exit(0);
//                            }
//                        }
//
//                    }
////                    Product p = gaSimpleRes.get(0);
//////
//////                    System.out.println(p.getSelectedNumber());
//////                    System.out.println(p);
////                    IVecInt prod = new VecInt(p.size());
////                    prod.push(1);
////                    for (int j = 2; j <= 800; j++) {
////                        if (Math.random() > 0.8) {
////                            prod.push(j);
////                        } else {
////                            prod.push(-j);
////                        }
////                    }
////                    //reasonerSAT.getSolver().reset();
//////                    toProduct(dimacsSolver.findModel(productToInt(p)));
////                    Product tp = toProduct(dimacsSolver.findModel(prod));
////                    System.out.println(tp.getSelectedNumber() + " "+tp);
////                    nbsuc++;
//                } catch (Exception e) {
//                    nbfail++;
//                }
//                Thread.sleep(100);
//            }
//
//
//            System.exit(0);

            if (!noCoverage) {
                System.out.println("done, coverage...");
            } else {
                System.out.println("done.");
            }


            double[] runCoverageGA = null;
            double[] fitnessSimpleGA = null;
            if (!noCoverage) {
                computeProductsCoverage(gaSimpleRes, validPairs);
                runCoverageGA = new double[coverageValuesSimpleGA.length];
                for (int j = 0; j < nbProds; j++) {
                    double cov = gaSimpleRes.get(j).getCoverage();
                    coverageValuesSimpleGA[j] += cov;
                    runCoverageGA[j] = cov;
                }
                fitnessSimpleGA = computeFitnessSums(gaSimpleRes, SimilarityTechnique.JACCARD_DISTANCE);
                for (int j = 0; j < fitnessValuesSimpleGA.length; j++) {
                    fitnessValuesSimpleGA[j] += fitnessSimpleGA[j];

                }
            }

            //run values
            if (!noCoverage) {
                if (!onlyGA) {
                    writeCoverageAndFitnessValuesToFile(outputDir + fmFileName + "_GA-UnpredictableProducts-" + sNbProds + "prods-" + timeAllowed + "ms-run" + (i + 1) + ".dat", runCoverageUnpredictable, fitnessUnpredictable);
                    writeCoverageAndFitnessValuesToFile(outputDir + fmFileName + "_GA-UnpredictableProductsPrioritized-" + sNbProds + "prods-" + timeAllowed + "ms-run" + (i + 1) + ".dat", runCoverageUnpredictablePrioritized, fitnessUnpredictablePrioritized);
                }
                writeCoverageAndFitnessValuesToFile(outputDir + fmFileName + "_GA-SimpleGAProducts-" + sNbProds + "prods-" + timeAllowed + "ms-run" + (i + 1) + ".dat", runCoverageGA, fitnessSimpleGA);
            }
            //save products

            if (!onlyGA) {
                writeProductsToFile(outputDir + fmFileName + "_GA-UnpredictableProducts-" + sNbProds + "prods-" + timeAllowed + "ms-" + "run" + (i + 1) + ".products.csv", unpredictableProducts, featuresMap, featuresList);
                writeProductsToFile(outputDir + fmFileName + "_GA-UnpredictablePrioritized-" + sNbProds + "prods-" + timeAllowed + "ms-" + "run" + (i + 1) + ".products.csv", simOptiPrioritizedUnpredictable, featuresMap, featuresList);
            }
            writeProductsToFile(outputDir + fmFileName + "_GA-SimpleGAProducts-" + sNbProds + "prods-" + timeAllowed + "ms-" + "run" + (i + 1) + ".products.csv", gaSimpleRes, featuresMap, featuresList);
        }

        if (!noCoverage) {
            for (int i = 0; i < nbProds; i++) {
                if (!onlyGA) {
                    coverageValuesUnpredictable[i] /= runs;
                    coverageValuesUnpredictablePrioritized[i] /= runs;

                    fitnessValuesUnpredictable[i] /= runs;
                    fitnessValuesUnpredictablePrioritized[i] /= runs;
                }
                coverageValuesSimpleGA[i] /= runs;
                fitnessValuesSimpleGA[i] /= runs;
            }
        }

        if (!noCoverage) {
            if (!onlyGA) {
                writeCoverageAndFitnessValuesToFile(outputDir + fmFileName + "_GA-UnpredictableProducts-" + sNbProds + "prods-" + timeAllowed + "ms-" + runs + "runs.dat", coverageValuesUnpredictable, fitnessValuesUnpredictable);
            }
            writeCoverageAndFitnessValuesToFile(outputDir + fmFileName + "_GA-UnpredictableProductsPrioritized-" + sNbProds + "prods-" + timeAllowed + "ms-" + runs + "runs.dat", coverageValuesUnpredictablePrioritized, fitnessValuesUnpredictablePrioritized);
            writeCoverageAndFitnessValuesToFile(outputDir + fmFileName + "_GA-SimpleGAProducts-" + sNbProds + "prods-" + timeAllowed + "ms-" + runs + "runs.dat", coverageValuesSimpleGA, fitnessValuesSimpleGA);
        }
    }

//    public void allPossiblePairs(String fmFile, boolean dimacs) {
//        try {
//            if (!new File(fmFile).exists()) {
//                throw new ParameterException("The specified FM file does not exist");
//            }
//
//            this.predictable = false;
//            this.dimacs = dimacs;
//            this.dimacsFile = fmFile;
//            if (!dimacs) {
//                fm = loadFeatureModel(fmFile);
//                fm.loadModel();
//                reasonerSAT = new FMReasoningWithSAT("MiniSAT", fm, SATtimeout);
//                reasonerSAT.init();
//            } else {
//                dimacsSolver = SolverFactory.instance().createSolverByName("MiniSAT");
//                dimacsSolver.setTimeout(SATtimeout);
//                DimacsReader dr = new DimacsReader(dimacsSolver);
//                dr.parseInstance(new FileReader(fmFile));
//            }
//
//            List<Integer> featuresList = new ArrayList<Integer>();
//            Map<Integer, String> featuresMap = new HashMap<Integer, String>();
//            Map<String, Integer> featuresMapRev = new HashMap<String, Integer>();
//
//            if (!dimacs) {
//                computeFeatures(reasonerSAT, featuresMap, featuresMapRev, featuresList, false, null);
//            } else {
//                computeFeatures(null, featuresMap, featuresMapRev, featuresList, true, fmFile);
//            }
//
//
//
//            List<FeaturesPair> pairs = new ArrayList<FeaturesPair>();
//
//            for (int i = 0; i < featuresList.size(); i++) {
//                for (int j = 0; j < featuresList.size(); j++) {
//                    if (j > i) {
//                        int left = featuresList.get(i);
//                        int right = featuresList.get(j);
//                        if (Math.abs(left) != Math.abs(right)) {
//                            FeaturesPair pair = new FeaturesPair(left, right);
//                            //pairs.add(pair);
//                            System.err.println(pair.getX() + ";" + pair.getY());
//                        }
//                    }
//
//                }
//                System.out.println(i);
//
//
//
//            }
//
//
//        } catch (Exception ex) {
//            Logger.getLogger(SPL.class.getName()).log(Level.SEVERE, null, ex);
//            System.out.println(
//                    "error");
//        }
//
//    }
    public void findCoreFeatures(String fmFile, boolean dimacs) {
        try {
            if (!new File(fmFile).exists()) {
                throw new ParameterException("The specified FM file does not exist");
            }

            this.predictable = false;
            this.dimacs = dimacs;
            this.dimacsFile = fmFile;
            if (!dimacs) {
                fm = loadFeatureModel(fmFile);
                fm.loadModel();
                reasonerSAT = new FMReasoningWithSAT("MiniSAT", fm, SATtimeout);
                reasonerSAT.init();
            } else {
                dimacsSolver = SolverFactory.instance().createSolverByName("MiniSAT");
                dimacsSolver.setTimeout(SATtimeout);
                DimacsReader dr = new DimacsReader(dimacsSolver);
                dr.parseInstance(new FileReader(fmFile));
            }

            List<Integer> featuresList = new ArrayList<Integer>();
            Map<Integer, String> featuresMap = new HashMap<Integer, String>();
            Map<String, Integer> featuresMapRev = new HashMap<String, Integer>();

            if (!dimacs) {
                computeFeatures(reasonerSAT, featuresMap, featuresMapRev, featuresList, false, null);
            } else {
                computeFeatures(null, featuresMap, featuresMapRev, featuresList, true, fmFile);
            }


            if (!dimacs) {
                reasonerSAT.init();
                ((Solver) reasonerSAT.getSolver()).setOrder(order);
                solverIterator = new ModelIterator(reasonerSAT.getSolver());
                solverIterator.setTimeoutMs(iteratorTimeout);
            } else {
                ((Solver) dimacsSolver).setOrder(order);
                solverIterator = new ModelIterator(dimacsSolver);
                solverIterator.setTimeoutMs(iteratorTimeout);
            }


            int a = 1;

            while (a < 5) {

                Product p = getUnpredictableProduct();
                IVecInt t = new VecInt();

                this.predictable = false;
                this.dimacs = dimacs;
                this.dimacsFile = fmFile;
                if (!dimacs) {
                    fm = loadFeatureModel(fmFile);
                    fm.loadModel();
                    reasonerSAT = new FMReasoningWithSAT("MiniSAT", fm, SATtimeout);
                    reasonerSAT.init();
                } else {
                    dimacsSolver = SolverFactory.instance().createSolverByName("MiniSAT");
                    dimacsSolver.setTimeout(SATtimeout);
                    DimacsReader dr = new DimacsReader(dimacsSolver);
                    dr.parseInstance(new FileReader(fmFile));
                }
                //System.out.println(p.size());
                for (Integer i : p) {
                    t.push(i);
                    //System.out.println(i);
                }



                System.out.println(dimacsSolver.isSatisfiable(t));

                System.out.println("");
                for (int i = 1; i <= 6888; i++) {
                    if (!p.contains(i) && !p.contains(-i)) {
                        System.out.println(featuresMap.get(i));
                    }


                }
                System.exit(0);
            }

            List<String> f = new ArrayList<String>();

            for (int i = 1; i <= featuresMap.size(); i++) {
                IVecInt prod = new VecInt();
                prod.push(i);
                if (!dimacsSolver.isSatisfiable(prod)) {
//                    IVecInt prod2 = new VecInt();
//                    prod2.push(i);
//                    if (reasonerSAT.getSolver().isSatisfiable(prod2)) {
//                       // f.add(featuresMap.get(i));
                    System.out.println(featuresMap.get(i));
//                    }


                }

            }

            //System.out.println(f.equals(reasonerSAT.allFreeFeatures(null)));
        } catch (Exception ex) {
            Logger.getLogger(SPL.class.getName()).log(Level.SEVERE, null, ex);
            System.out.println(
                    "error");
        }
    }

//    public boolean containPair(String file, FeaturesPair pair) {
//        try {
//            BufferedReader in = new BufferedReader(new FileReader(file));
//            String line;
//
//            while ((line = in.readLine()) != null) {
//                if (line.equals(pair.getX() + ";" + pair.getY()) || line.equals(pair.getY() + ";" + pair.getX())) {
//                    in.close();
//                    return true;
//                }
//            }
//
//            in.close();
//
//
//        } catch (Exception ex) {
//            Logger.getLogger(SPL.class.getName()).log(Level.SEVERE, null, ex);
//        }
//        return false;
//    }
//    public void computeProductPairs(String fmFile, boolean dimacs, String conf) {
//
//        try {
//            if (!new File(fmFile).exists()) {
//                throw new ParameterException("The specified FM file does not exist");
//            }
//
//            this.predictable = false;
//            this.dimacs = dimacs;
//            this.dimacsFile = fmFile;
//            if (!dimacs) {
//                fm = loadFeatureModel(fmFile);
//                fm.loadModel();
//                reasonerSAT = new FMReasoningWithSAT("MiniSAT", fm, SATtimeout);
//                reasonerSAT.init();
//            } else {
//                dimacsSolver = SolverFactory.instance().createSolverByName("MiniSAT");
//                dimacsSolver.setTimeout(SATtimeout);
//                DimacsReader dr = new DimacsReader(dimacsSolver);
//                dr.parseInstance(new FileReader(fmFile));
//            }
//
//
//
//
//            List<Integer> featuresList = new ArrayList<Integer>();
//            Map<Integer, String> featuresMap = new HashMap<Integer, String>();
//            Map<String, Integer> featuresMapRev = new HashMap<String, Integer>();
//
//            if (!dimacs) {
//                computeFeatures(reasonerSAT, featuresMap, featuresMapRev, featuresList, false, null);
//            } else {
//                computeFeatures(null, featuresMap, featuresMapRev, featuresList, true, fmFile);
//            }
//
//
//            List<Integer> prodFeat = new ArrayList<Integer>();
//
//
//            BufferedReader in = new BufferedReader(new FileReader(conf));
//            String line;
//
//            while ((line = in.readLine()) != null) {
//                if (!line.isEmpty() && !line.contains("#")) {
//                    String feature = line.substring(0, line.indexOf("="));
//                    feature = feature.substring(feature.indexOf("_") + 1, feature.length());
//                    String val = line.substring(line.indexOf("=") + 1, line.length()).trim();
//                    int nf = featuresMapRev.get(feature);
//                    if (!val.equals("\"\"")) {
//                        prodFeat.add(nf);
//                    } else {
//                        prodFeat.add(-nf);
//                    }
//                }
//
//            }
//
//
////pairs on partial
//
//            for (int i = 0; i < prodFeat.size(); i++) {
//                for (int j = 0; j < prodFeat.size(); j++) {
//                    if (j > i) {
//                        int left = prodFeat.get(i);
//                        int right = prodFeat.get(j);
//                        if (Math.abs(left) != Math.abs(right)) {
//                            FeaturesPair pair = new FeaturesPair(left, right);
//                            //pairs.add(pair);
//                            //if (!containPair("/home/chris/2.6.28.6-icse11.dimacs.validpairs", pair)) {
//                            System.out.println(pair.getX() + ";" + pair.getY());
//                            //}
//
//                        }
//                    }
//
//                }
//
//            }
//            in.close();
//
//
//
//        } catch (Exception ex) {
//            Logger.getLogger(SPL.class.getName()).log(Level.SEVERE, null, ex);
//            System.out.println(
//                    "error");
//        }
//    }
    public void isDimacsValid(String fmFile, boolean dimacs, String dirconf) {

        try {
            if (!new File(fmFile).exists()) {
                throw new ParameterException("The specified FM file does not exist");
            }

            this.predictable = false;
            this.dimacs = dimacs;
            this.dimacsFile = fmFile;
            if (!dimacs) {
                fm = loadFeatureModel(fmFile);
                fm.loadModel();
                reasonerSAT = new FMReasoningWithSAT("MiniSAT", fm, SATtimeout);
                reasonerSAT.init();
            } else {
                dimacsSolver = SolverFactory.instance().createSolverByName("MiniSAT");
                dimacsSolver.setTimeout(SATtimeout);
                DimacsReader dr = new DimacsReader(dimacsSolver);
                dr.parseInstance(new FileReader(fmFile));
            }




            List<Integer> featuresList = new ArrayList<Integer>();
            Map<Integer, String> featuresMap = new HashMap<Integer, String>();
            Map<String, Integer> featuresMapRev = new HashMap<String, Integer>();

            if (!dimacs) {
                computeFeatures(reasonerSAT, featuresMap, featuresMapRev, featuresList, false, null);
            } else {
                computeFeatures(null, featuresMap, featuresMapRev, featuresList, true, fmFile);
            }


            File[] confs = new File(dirconf).listFiles();

            for (File conf : confs) {

                BufferedReader in = new BufferedReader(new FileReader(conf));
                String line;
                List<Integer> integs = new ArrayList<Integer>();

                IVecInt prod = new VecInt(6888);
                while ((line = in.readLine()) != null) {
                    if (!line.isEmpty() && !line.contains("#")) {
                        String feature = line.substring(0, line.indexOf("="));
                        feature = feature.substring(feature.indexOf("_") + 1, feature.length());
                        String val = line.substring(line.indexOf("=") + 1, line.length()).trim();
                        int nf = featuresMapRev.get(feature);
                        if (!val.equals("\"\"")) {
                            prod.push(nf);
                        } else {
                            prod.push(-nf);
                        }
                        integs.add(Math.abs(nf));

                    }
//                Integer i = Integer.parseInt(line);
//
////                if (i == 1){
////                    prod.push(-i);
////                integs.add((Integer) ((int) Math.abs(-i)));
////                }
////                else{
//                prod.push(i);
//                integs.add((Integer) ((int) Math.abs(i)));
//                System.out.println(featuresMap.get((int) Math.abs(i)));
//                }

//                System.out.println(i + "->" + dimacsSolver.isSatisfiable(prod));
                }

//                for (int i = 1; i <= 6888; i++) {
//                    if (!integs.contains(i)) {
//                        prod.push(-i);
//                    }
//
//                }

                //System.out.println(prod.size());
                in.close();
                System.out.println(conf.getName() + ":" + dimacsSolver.isSatisfiable(prod));


            }
        } catch (Exception ex) {
            Logger.getLogger(SPL.class.getName()).log(Level.SEVERE, null, ex);
            System.out.println(
                    "error");
        }

    }

    public IVecInt productToInt(Product p) {
        IVecInt prod = new VecInt(p.size() - 1);
        List<Integer> productList = GA.productToList(p);
        int j = 0;
        for (Integer n : productList) {
            if (j++ <= p.size() / 2) {
                prod.push(n);
            }

        }
        return prod;
    }

     

    public FeatureModel loadFeatureModel(String fmFile) {
        return new XMLFeatureModel(fmFile, XMLFeatureModel.USE_VARIABLE_NAME_AS_ID);
    }

    public List<Product> getUnpredictableProducts(int count) throws Exception {
        List<Product> products = new ArrayList<Product>(count);

        while (products.size() < count) {

            try {
                if (solverIterator.isSatisfiable()) {
                	
                	//----------------------------Set order---------------------------------
                	int rand = (new Random()).nextInt(3);
                	IOrder order;
                     if (rand == 0) {
                         order = new RandomWalkDecorator(new VarOrderHeap(new NegativeLiteralSelectionStrategy()), 1);
                     } else if (rand == 1) {
                         order = new RandomWalkDecorator(new VarOrderHeap(new PositiveLiteralSelectionStrategy()), 1);
                     } else {
                         order = new RandomWalkDecorator(new VarOrderHeap(new RandomLiteralSelectionStrategy()), 1);
                     }
                     
                	((Solver) solverIterator).setOrder(order); 
                	//----------------------------Set order end ---------------------------------
                	
                	
                    Product product = toProduct(solverIterator.findModel());

                    int selected = 0;
                 	
                 	for (Integer i : product) {
                 		if (i > 0) selected++;
                 	}
                 	
//                 	System.out.println("# Selected featues" + selected);
                 	
                    if (!products.contains(product)) {
                        products.add(product);
                    }

                } else {
                	System.out.println("Reinitialize solvers");
                    if (!dimacs) {
                        reasonerSAT.init();
                        if (!predictable) {
                            ((Solver) reasonerSAT.getSolver()).setOrder(order);
                        }
                        solverIterator = new ModelIterator(reasonerSAT.getSolver());
                        solverIterator.setTimeoutMs(iteratorTimeout);

                    } else {
                        dimacsSolver = SolverFactory.instance().createSolverByName("MiniSAT");
                        dimacsSolver.setTimeout(SATtimeout);
                        DimacsReader dr = new DimacsReader(dimacsSolver);
                        dr.parseInstance(new FileReader(dimacsFile));
                        if (!predictable) {
                            ((Solver) dimacsSolver).setOrder(order);
                        }
                        solverIterator = new ModelIterator(dimacsSolver);
                        solverIterator.setTimeoutMs(iteratorTimeout);
                    }
                }
            } catch (TimeoutException e) {
            }
        }
        return products;
    }

   
        
    
    public List<Product> getUnpredictableProductsSetOrderDuringRun(int count) throws Exception {
        List<Product> products = new ArrayList<Product>(count);

        while (products.size() < count) {

            try {
                if (solverIterator.isSatisfiable()) {
                	
                	// Reset orders, should be kept
                	int rand = (new Random()).nextInt(3);
                	IOrder order;
                     if (rand == 0) {
                         order = new RandomWalkDecorator(new VarOrderHeap(new NegativeLiteralSelectionStrategy()), 1);
                     } else if (rand == 1) {
                         order = new RandomWalkDecorator(new VarOrderHeap(new PositiveLiteralSelectionStrategy()), 1);
                     } else {
                         order = new RandomWalkDecorator(new VarOrderHeap(new RandomLiteralSelectionStrategy()), 1);
                     }
                     
                	((Solver) solverIterator).setOrder(order); 
                	
                    Product product = toProduct(solverIterator.findModel());

                    int selected = 0;
                 	
                 	for (Integer i : product) {
                 		if (i > 0) selected++;
                 	}                	
                 	                 	
                    if (!products.contains(product)) {
                        products.add(product);
                        //System.out.println("# Selected featues" + selected);
//                        System.out.println( selected);
                    }

                } else {
                	System.out.println("Reinitialize solvers");
                    if (!dimacs) {
                        reasonerSAT.init();
                        if (!predictable) {
                            ((Solver) reasonerSAT.getSolver()).setOrder(order);
                        }
                        solverIterator = new ModelIterator(reasonerSAT.getSolver());
                        solverIterator.setTimeoutMs(iteratorTimeout);

                    } else {
                        dimacsSolver = SolverFactory.instance().createSolverByName("MiniSAT");
                        dimacsSolver.setTimeout(SATtimeout);
                        DimacsReader dr = new DimacsReader(dimacsSolver);
                        dr.parseInstance(new FileReader(dimacsFile));
                        if (!predictable) {
                            ((Solver) dimacsSolver).setOrder(order);
                        }
                        solverIterator = new ModelIterator(dimacsSolver);
                        solverIterator.setTimeoutMs(iteratorTimeout);
                    }
                }
            } catch (TimeoutException e) {
            }
        }
        return products;
    }
    
   public int selectedFeature (Product product) {
	   int selected = 0;
    	
    	for (Integer i : product) {
    		if (i>0) selected++;
    	}
    	return selected;
    	
   }
	
   /**
    * 
    * @param count
    * @return
    * @throws Exception
    */
    public List<Product> getRandomProductsSMT(int count) throws Exception {
        List<Product> products = new ArrayList<Product>(count);        	
        List<Integer> visited = new ArrayList<Integer>();
        
        while (products.size() < count) {
//        	System.out.println(products.size());        	
            try {   
            	
            	int randomInt = PseudoRandom.randInt(mandatoryFeaturesIndices.size(), numFeatures - deadFeaturesIndices.size());
               
            	Binary binary = ftz.solveWithD(randomInt);// 得到一个解
            
//            	while (binary == null) {	//visited.contains(randomInt)
//            		randomInt = PseudoRandom.randInt(mandatoryFeaturesIndices.size(), numFeatures - deadFeaturesIndices.size());
//		    		binary = ftz.solveWithD(randomInt);// 得到一个解
////		    		System.out.println(randomInt);
//		    	}
            	
            	if (binary == null) {            		
            		Product product = toProduct(solverIterator.findModel());
                    if (!products.contains(product)) {
                       products.add(product);
                    }  
                    
            	} else {

            		Product product = toProduct(binary);
            		
            		if (!products.contains(product)) {
	    		        products.add(product);  
	    		        visited.add(randomInt);
	    		    }    
            		 
            	} // if    

            } catch (TimeoutException e) {
            	
            	Product product = toProduct(solverIterator.findModel());
            	if (!products.contains(product)) {
    		        products.add(product);  
    		
    		    }  
            	
            }
        }
        return products;
    }
    
    
   
    
   
    public int numViolatedConstraints(Binary b, HashSet<Integer> blacklist) {

        //IVecInt v = bitSetToVecInt(b);
    	List<List<Integer>> constraints =  featureModelConstraints;

        int s = 0;
        for (List<Integer> constraint : constraints) {
            boolean sat = false;

            for (Integer i : constraint) {
                int abs = (i < 0) ? -i : i;
                boolean sign = i > 0;
                if (b.getIth(abs - 1) == sign) {
                    sat = true;
                } else {
                    blacklist.add(abs);
                }
            }
            if (!sat) {
                s++;
            }

        }

        return s;
    }
    public Binary randomProductAssume(Binary bin) {
    	
  		HashSet<Integer> blacklist = new HashSet<Integer>();  	   
  	       
        int violated = numViolatedConstraints(bin, blacklist);
        
        if (violated > 0) {
            IVecInt iv = new VecInt();

            for (int j : featureIndicesAllowedFlip) {
                int feat = j + 1;

                if (!blacklist.contains(feat)) {
                    iv.push(bin.bits_.get(j) ? feat : -feat);
                }

            }

            boolean[] prod = randomProductFromSolution(iv);
            
            for (int j = 0; j < prod.length; j++) {
                bin.setIth(j, prod[j]);
            }
        }
  	    
        return bin;
      }
    
    
    public boolean[] randomProductFromSolution(IVecInt ivi) {        

        boolean[] prod = new boolean[numFeatures];
        for (int i = 0; i < prod.length; i++) {
            prod[i] = randomGenerator.nextBoolean();
        }

        for (Integer f : this.mandatoryFeaturesIndices) {
        	prod[f] = true;
        }

        for (Integer f : this.deadFeaturesIndices) {
        	prod[f] = false;
        }
                

        try {    
        	
//        	int rand = (new Random()).nextInt(3);
//        	IOrder order;
//             if (rand == 0) {
//                 order = new RandomWalkDecorator(new VarOrderHeap(new NegativeLiteralSelectionStrategy()), 1);
//             } else if (rand == 1) {
//                 order = new RandomWalkDecorator(new VarOrderHeap(new PositiveLiteralSelectionStrategy()), 1);
//             } else {
//                 order = new RandomWalkDecorator(new VarOrderHeap(new RandomLiteralSelectionStrategy()), 1);
//             }
             
        	((Solver) solverIterator).setOrder(order);
        	
            if (solverIterator.isSatisfiable()) {
                int[] i = solverIterator.findModel(ivi);
                for (int j = 0; j < i.length; j++) {
                    int feat = i[j];

                    int posFeat = feat > 0 ? feat : -feat;

                    if (posFeat > 0) {
                        prod[posFeat - 1] = feat > 0;
                    }

                }

            } 
            

        } catch (Exception e) {
        	
        	for (Integer f : this.mandatoryFeaturesIndices) {
              	prod[f] = true;
              }

              for (Integer f : this.deadFeaturesIndices) {
              	prod[f] = false;
              }
//              e.printStackTrace();
      	    return prod;
        }

        return prod;
    }
    
    /**
     * Get random products using Random + Repair
     * @param count
     * @return
     * @throws Exception
     */
    public List<Product> getRandomProducts(int count,Map<Integer, String> featuresMap, List<Integer> featuresList,double p) throws Exception {
        List<Product> products = new ArrayList<Product>(count);

        
        while (products.size() < count) {      
        	Product product = null;

        	if (randomGenerator.nextDouble() <= p) {
     
	        	Binary randomBinary = new Binary(numFeatures); // 随机产生一个二进制串   	        	

	            for (Integer f : this.mandatoryFeaturesIndices) {
	            	randomBinary.setIth(f, true);               	
	             }

	             for (Integer f : this.deadFeaturesIndices) {
	            	 randomBinary.setIth(f, false);    
	             }
	             
	        	Binary repaired = (Binary) repairSolver.execute(randomBinary);        	
	            product = toProduct(repaired);   
	            
	            if (!isValidProduct(product, featuresMap, featuresList)) { // 不可行
	        	   product = toProduct(solverIterator.findModel());
	            }
	        	   
        	} else {
        	
	        	if (solverIterator.isSatisfiable()) {
	        		product = toProduct(solverIterator.findModel());
	        	}
        	}
        	
            if (!products.contains(product) ) { 
                products.add(product);
            } 
            
        }
     
        return products;
    }
    
    
    /**
     * Get random products using Random + Repair
     * @param count
     * @return
     * @throws Exception
     */
    public List<Product> getRandomProductsAssume(int count,Map<Integer, String> featuresMap, List<Integer> featuresList,double p) throws Exception {
        List<Product> products = new ArrayList<Product>(count);

        while (products.size() < count) {      
        	Product product = null;

        	if (randomGenerator.nextDouble() <= p) {
     
	        	Binary randomBinary = new Binary(numFeatures); // 随机产生一个二进制串   	        	

	            for (Integer f : this.mandatoryFeaturesIndices) {
	            	randomBinary.setIth(f, true);               	
	             }

	             for (Integer f : this.deadFeaturesIndices) {
	            	 randomBinary.setIth(f, false);    
	             }
	             
	        	Binary repaired = randomProductAssume(randomBinary);        	
	            product = toProduct(repaired);   
	       
	            
	           if (!isValidProduct(product, featuresMap, featuresList)) { // 不可行
	        	   product = toProduct(solverIterator.findModel());
	           }
	        	   
        	} else {
        	
	        	if (solverIterator.isSatisfiable()) {
	        		product = toProduct(solverIterator.findModel());
	        	}
        	}
        	
            if (!products.contains(product) ) { 
                products.add(product);
            } 
            
        }
     
        return products;
    }
    /**
     * Get random products using Random + Repair
     * @param count
     * @return
     * @throws Exception
     */
    public Product getRandomProducts(double p) throws Exception {
              
        	Product product = null;
        	
        	if (randomGenerator.nextDouble() <= p) {
//        		System.out.println("Repair");
	        	 	             
	            Binary randomBinary = new Binary(numFeatures); // 随机产生一个二进制串   	
	            for (Integer f : this.mandatoryFeaturesIndices) {
	            	randomBinary.setIth(f, true);               	
	             }

	             for (Integer f : this.deadFeaturesIndices) {
	            	 randomBinary.setIth(f, false);    
	             }
	             
	        	Binary repaired = (Binary) repairSolver.execute(randomBinary);        	
	            product = toProduct(repaired);   
	            
	            if (!isValidProduct(product)) {
	            	product = toProduct(solverIterator.findModel());
	            }
	            
        	} else {
        		
        		// Reset orders, should be kept
            	int rand = (new Random()).nextInt(3);
            	IOrder order;
                 if (rand == 0) {
                     order = new RandomWalkDecorator(new VarOrderHeap(new NegativeLiteralSelectionStrategy()), 1);
                 } else if (rand == 1) {
                     order = new RandomWalkDecorator(new VarOrderHeap(new PositiveLiteralSelectionStrategy()), 1);
                 } else {
                     order = new RandomWalkDecorator(new VarOrderHeap(new RandomLiteralSelectionStrategy()), 1);
                 }
                 
            	((Solver) solverIterator).setOrder(order); 
            	
            	
	        	if (solverIterator.isSatisfiable()) {
	        		product = toProduct(solverIterator.findModel());
	        	}
        	}        	    
     
        return product;
    }

    /**
     * 将Product转换成Binary
     * @param vector
     * @return
     */
    public Binary Product2Bin(Product prod) {

    	Binary bin = new Binary(prod.size());    	    
        
        for (Integer i:prod) {
        	
        	if (i > 0){
        		bin.setIth(i-1, true);
        	} else {
        		bin.setIth(Math.abs(i)-1, false);
        	}
        		
        } // for i
        return bin;
    }
    
    /**
     * Get random products using Random + Repair
     * @param count
     * @return
     * @throws Exception
     */
    public Product repairProducts(Product prod, double p) throws Exception {
              
        	Product product = null;
        	
        	if (randomGenerator.nextDouble() <= p) {
	        	 	             
	            Binary randomBinary =  Product2Bin(prod) ;  	            
	            
	            for (Integer f : this.mandatoryFeaturesIndices) {
	            	randomBinary.setIth(f, true);               	
	             }

	             for (Integer f : this.deadFeaturesIndices) {
	            	 randomBinary.setIth(f, false);    
	             }
	             
	        	Binary repaired = (Binary) repairSolver.execute(randomBinary);     // ProbSAT	             
//	        	Binary repaired = randomProductAssume(randomBinary);   // SAT4J
	            
	            product = toProduct(repaired);   

	            if (!isValidProduct(product)) {
//	            	System.out.println("Invalid after repairing");
	            	
//	            	int rand = (new Random()).nextInt(2);
//                	IOrder order;
//                     if (rand == 0) {
//                         order = new RandomWalkDecorator(new VarOrderHeap(new NegativeLiteralSelectionStrategy()), 1);
//                     } else if (rand == 1) {
//                         order = new RandomWalkDecorator(new VarOrderHeap(new PositiveLiteralSelectionStrategy()), 1);
//                     } else {
//                         order = new RandomWalkDecorator(new VarOrderHeap(new RandomLiteralSelectionStrategy()), 1);
//                     }
//                    
//	            	((Solver) solverIterator).setOrder(order); 
	            	
	            	product = toProduct(solverIterator.findModel());	            	
//	            	product = toProduct(randomProductAssume(repaired));   // SAT4J

	            }
	            
        	} else {
	        	if (solverIterator.isSatisfiable()) {
	        		
	        		int rand = (new Random()).nextInt(3);
                	IOrder order;
                     if (rand == 0) {
                         order = new RandomWalkDecorator(new VarOrderHeap(new NegativeLiteralSelectionStrategy()), 1);
                     } else if (rand == 1) {
                         order = new RandomWalkDecorator(new VarOrderHeap(new PositiveLiteralSelectionStrategy()), 1);
                     } else {
                         order = new RandomWalkDecorator(new VarOrderHeap(new RandomLiteralSelectionStrategy()), 1);
                     }
                     
	        		((Solver) solverIterator).setOrder(order); 
	        		
	        		product = toProduct(solverIterator.findModel());
	        	}
        	}
        	
                             
     
        return product;
    }

    
    public Product getUnpredictableProduct(Product startProduct) throws Exception {
        Product product = null;
        while (product == null) {
            try {
                if (solverIterator.isSatisfiable()) {
//                	int rand = (new Random()).nextInt(3);
//                	IOrder order;
//                     if (rand == 0) {
//                         order = new RandomWalkDecorator(new VarOrderHeap(new NegativeLiteralSelectionStrategy()), 1);
//                     } else if (rand == 1) {
//                         order = new RandomWalkDecorator(new VarOrderHeap(new PositiveLiteralSelectionStrategy()), 1);
//                     } else {
//                         order = new RandomWalkDecorator(new VarOrderHeap(new RandomLiteralSelectionStrategy()), 1);
//                     }
//                     
//                	((Solver) solverIterator).setOrder(order);                	         
//                	System.out.println("# Selected featues before " + this.selectedFeature(startProduct));
//                    product = toProduct(solverIterator.findModel(productToIntVec(startProduct)));    
                    product = toProduct(solverIterator.findModel());     
//                    System.out.println("# Selected featues after " + this.selectedFeature(product));
                    
                } else {
                	System.out.println("reinitialize solvers in getUnpredictableProduct()");
                    if (!dimacs) {
                        reasonerSAT.init();
                        if (!predictable) {
                            ((Solver) reasonerSAT.getSolver()).setOrder(order);
                        }
                        solverIterator = new ModelIterator(reasonerSAT.getSolver());
                        solverIterator.setTimeoutMs(iteratorTimeout);
                    } else {
                        dimacsSolver = SolverFactory.instance().createSolverByName("MiniSAT");
                        dimacsSolver.setTimeout(SATtimeout);
                        DimacsReader dr = new DimacsReader(dimacsSolver);
                        dr.parseInstance(new FileReader(dimacsFile));
                        if (!predictable) {
                            ((Solver) dimacsSolver).setOrder(order);
                        }
                        solverIterator = new ModelIterator(dimacsSolver);
                        solverIterator.setTimeoutMs(iteratorTimeout);
                    }
                }
            } catch (TimeoutException e) {
            }
        }
        return product;
    }

    public Product getUnpredictableProduct() throws Exception {
        Product product = null;
        while (product == null) {
            try {
                if (solverIterator.isSatisfiable()) {
                	
                	//-----------------------Set order-----------------------
                	int rand = (new Random()).nextInt(3);
                	IOrder order;
                     if (rand == 0) {
                         order = new RandomWalkDecorator(new VarOrderHeap(new NegativeLiteralSelectionStrategy()), 1);
                     } else if (rand == 1) {
                         order = new RandomWalkDecorator(new VarOrderHeap(new PositiveLiteralSelectionStrategy()), 1);
                     } else {
                         order = new RandomWalkDecorator(new VarOrderHeap(new RandomLiteralSelectionStrategy()), 1);
                     }
                     
                	((Solver) solverIterator).setOrder(order);                	         
                	//-----------------------Set order (end)-----------------------
                	
                	
                    product = toProduct(solverIterator.findModel());     
             
                } else {
                	System.out.println("reinitialize solvers in getUnpredictableProduct()");
                    if (!dimacs) {
                        reasonerSAT.init();
                        if (!predictable) {
                            ((Solver) reasonerSAT.getSolver()).setOrder(order);
                        }
                        solverIterator = new ModelIterator(reasonerSAT.getSolver());
                        solverIterator.setTimeoutMs(iteratorTimeout);
                    } else {
                        dimacsSolver = SolverFactory.instance().createSolverByName("MiniSAT");
                        dimacsSolver.setTimeout(SATtimeout);
                        DimacsReader dr = new DimacsReader(dimacsSolver);
                        dr.parseInstance(new FileReader(dimacsFile));
                        if (!predictable) {
                            ((Solver) dimacsSolver).setOrder(order);
                        }
                        solverIterator = new ModelIterator(dimacsSolver);
                        solverIterator.setTimeoutMs(iteratorTimeout);
                    }
                }
            } catch (TimeoutException e) {
            }
        }
        return product;
    }
    
    
    /**
     * 获得“可预测”的一组测试集
     * @param count
     * @param numberOfFeatures
     * @return
     * @throws Exception
     */
    public List<Product> getPredictableProducts(int count, int numberOfFeatures) throws Exception {
        List<Product> products = new ArrayList<Product>(count);
        while (products.size() < count) {
            try {
                if (solverIterator.isSatisfiable()) {
                    Product product = toProduct(solverIterator.model());
                    if (randomGenerator.nextInt(numberOfFeatures) == numberOfFeatures - 1) {

                        if (!products.contains(product)) {
                            products.add(product);
                        }
                    }
                } else {
                    if (!dimacs) {
                        reasonerSAT.init();
                        if (!predictable) {
                            ((Solver) reasonerSAT.getSolver()).setOrder(order);
                        }
                        solverIterator = new ModelIterator(reasonerSAT.getSolver());
                        solverIterator.setTimeoutMs(iteratorTimeout);
                    } else {
                        dimacsSolver = SolverFactory.instance().createSolverByName("MiniSAT");
                        dimacsSolver.setTimeout(SATtimeout);
                        DimacsReader dr = new DimacsReader(dimacsSolver);
                        dr.parseInstance(new FileReader(dimacsFile));
                        if (!predictable) {
                            ((Solver) dimacsSolver).setOrder(order);
                        }
                        solverIterator = new ModelIterator(dimacsSolver);
                        solverIterator.setTimeoutMs(iteratorTimeout);
                    }
                }

            } catch (TimeoutException e) {
            }
        }
        return products;
    }
    
    
    /**
     * 计算一个测试集覆盖的pairs
     * @param products
     * @return
     */
    public Set<TSet> computePairsCoveredByProducts(List<Product> products) {
        Set<TSet> coveredPairs = new HashSet<TSet>();
        for (Product product : products) {
            Set<TSet> productPairs = product.computeCoveredPairs(); // 每个测试用例覆盖的pairs
            coveredPairs.addAll(productPairs);// 不会加入相同的pairs
        }
        return coveredPairs;
    }

    /**
     * 计算一个测试集中，每个测试实例的（部分）覆盖率。注意：不是绝对覆盖率。如果t-set不准确，则覆盖率不太可靠
     * @param products
     * @param pairs
     */
    public void computeProductsPartialCoverage(List<Product> products, Set<TSet> pairs) {
        double pairsSize = pairs.size();
        Set<TSet> pairsCopy = new HashSet<TSet>(pairs);
        for (Product product : products) {
            int initialSize = pairsCopy.size();
            Set<TSet> productPairs = product.computePartialCoveredPairs(pairsCopy);
            pairsCopy.removeAll(productPairs);
            double removed = initialSize - pairsCopy.size();
            double coverage = removed / pairsSize * 100.0;
            product.setCoverage(coverage);
        }
        pairsCopy = null;
    }

    /**
     * 计算一个测试集中，每个测试实例的（部分）覆盖率。注意：不是绝对覆盖率。如果t-set不准确，则覆盖率不太可靠
     * @param products
     * @param pairs
     */
    public void computeProductsPartialFaults(List<Product> products, Set<TSet> pairs) {
        double pairsSize = pairs.size();
        Set<TSet> pairsCopy = new HashSet<TSet>(pairs);
        for (Product product : products) {
            int initialSize = pairsCopy.size();
            Set<TSet> productPairs = product.computePartialCoveredPairs(pairsCopy);
            pairsCopy.removeAll(productPairs);
            double removed = initialSize - pairsCopy.size();           
            product.setCoverage(removed);
        }
        
        pairsCopy = null;
    }
    
    /**
     * 计算每个测试用例的真正覆盖率。这些覆盖率的计算去除了重复覆盖的pair
     * @param products
     * @param pairs
     */
    public void computeProductsCoverage(List<Product> products, Set<TSet> pairs) {
        double pairsSize = pairs.size();
        Set<TSet> pairsCopy = new HashSet<TSet>(pairs);
        for (Product product : products) {
            int initialSize = pairsCopy.size();
            Set<TSet> productPairs = product.computeCoveredPairs();
            pairsCopy.removeAll(productPairs);
            double removed = initialSize - pairsCopy.size();
            double coverage = removed / pairsSize * 100.0;
            product.setCoverage(coverage);
        }
        pairsCopy = null;
    }

    /**
     * 对products重新洗牌，即打乱顺序
     * @param products
     */
    public void shuffle(List<Product> products) {
        List<Product> productsCopy = new ArrayList<Product>(products);
        int done = 0;
        while (done < products.size()) {
            int index = randomGenerator.nextInt(productsCopy.size());
            products.set(done++, productsCopy.get(index));
            productsCopy.remove(index);
        }
    }

    public void writeDimacsProductToFile(String outFile, Product product) throws Exception {
        BufferedWriter out = new BufferedWriter(new FileWriter(outFile));

        for (Integer i : product) {
            out.write(Integer.toString(i));
            //if (n < product.size()) {
            out.newLine();
            //}
        }
        out.close();
    }

    public Set<TSet> loadSerializedTSets(String inFile) {


        Set<TSet> tsets = null;
        try {



            FileInputStream fileIn = new FileInputStream(inFile);
            ObjectInputStream in = new ObjectInputStream(fileIn);

            tsets = (HashSet<TSet>) in.readObject();

            in.close();
            fileIn.close();

        } catch (ClassNotFoundException e) {
            e.printStackTrace();
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }

        return tsets;

    }

    public List<Product> loadSerializedProducts(String inFile) {


        List<Product> prods = null;
        try {



            FileInputStream fileIn = new FileInputStream(inFile);
            ObjectInputStream in = new ObjectInputStream(fileIn);

            prods = (ArrayList<Product>) in.readObject();

            in.close();
            fileIn.close();

        } catch (ClassNotFoundException e) {
            e.printStackTrace();
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }

        return prods;

    }

    public void serializeTSets(String outFile, Set<TSet> tsets) {
        try {


            FileOutputStream fileOut = new FileOutputStream(outFile);
            ObjectOutputStream out = new ObjectOutputStream(fileOut);

            out.writeObject(tsets);
            out.close();
            fileOut.close();

        } catch (Exception e) {
            e.printStackTrace();
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

    public void writeProductsToFile(String outFile, List<Product> products, Map<Integer, String> featuresMap, List<Integer> featuresList) throws Exception {
//        BufferedWriter out = new BufferedWriter(new FileWriter(outFile));

//        out.write("Feature\\Product;");
//
//        for (int i = 0; i < products.size(); i++) {
//            out.write("" + i + ";");
//        }
//
//        out.newLine();
//
//        int featuresCount = featuresList.size() / 2;
//        for (int i = 1; i <= featuresCount; i++) {
//            out.write(featuresMap.get(i) + ";");
//
//            for (Product p : products) {
//                for (Integer n : p) {
//                    if (Math.abs(n) == i) {
//                        if (n > 0) {
//                            out.write("X;");
//                        } else {
//                            out.write("-;");
//                        }
//                    }
//                }
//            }
//            out.newLine();
//        }
//        out.close();


        BufferedWriter out = new BufferedWriter(new FileWriter(outFile));

        int featuresCount = featuresList.size() / 2;
        for (int i = 1; i <= featuresCount; i++) {
            out.write(i + ":" + featuresMap.get(i));
            if (i < featuresCount) {
                out.write(";");
            }
        }
        out.newLine();
        for (Product product : products) {
            List<Integer> prodFeaturesList = new ArrayList<Integer>(product);
            Collections.sort(prodFeaturesList, new Comparator<Integer>() {

                @Override
                public int compare(Integer o1, Integer o2) {
                    return ((Integer) Math.abs(o1)).compareTo(((Integer) Math.abs(o2)));
                }
            });

            int done = 1;
            for (Integer feature : prodFeaturesList) {
                out.write((feature > 0 ? "X" : "-"));
                if (done < featuresCount) {
                    out.write(";");
                }
                done++;
            }

            out.newLine();
        }
        out.close();
    }

    
    /**
     * 将products写入文件
     * @param outFile
     * @param products
     * @throws Exception
     */
    public void writeProductsToFile(String outFile, List<Product> products) throws Exception {

      FileUtils.resetFile(outFile);
      
      BufferedWriter out = new BufferedWriter(new FileWriter(outFile));
          
//      out.write(products.size() + " products");
//      out.newLine();
      
      for (Product product : products) {
          List<Integer> prodFeaturesList = new ArrayList<Integer>(product);
          Collections.sort(prodFeaturesList, new Comparator<Integer>() {

              @Override
              public int compare(Integer o1, Integer o2) {
                  return ((Integer) Math.abs(o1)).compareTo(((Integer) Math.abs(o2)));
              }
          });

          int done = 1;
          for (Integer feature : prodFeaturesList) {
              out.write(Integer.toString(feature));   
              if (done < numFeatures) {
                  out.write(";");
              }
              done++;
          }

          out.newLine();
      }
      out.close();
  }
    
    /**
     * 从文件读取products
     * @param outFile
     * @param products
     * @throws Exception
     */
    public List<Product> loadProductsFromFile(String inFile) throws Exception {
    	List<Product> products = new  ArrayList <Product>();
    	
        BufferedReader in = new BufferedReader(new FileReader(inFile));
        String line;
       
        while ((line = in.readLine()) != null && !(line.isEmpty())) {
           
        	StringTokenizer tokenizer = new StringTokenizer(line, ";");
            Product product = new Product();     
            
            while (tokenizer.hasMoreTokens()) {
                String tok = tokenizer.nextToken().trim();
                product.add(Integer.parseInt(tok));
            }
             
            products.add(product);
          
        }       
        
        in.close();
        
    	return products;
   
  }
    
    /**
     * Write products into files
     * @param outFile
     * @param products
     * @throws Exception
     */
    public void writeDataToFile(String outFile, double data) throws Exception {

      FileUtils.resetFile(outFile);
      
      BufferedWriter out = new BufferedWriter(new FileWriter(outFile));
          
      out.write(Double.toString(data));
      
      out.close();

  }
    
    /**
     * Write data into files
     * @param outFile
     * @param products
     * @throws Exception
     */
    public void writeDataToFile(String outFile, double [] data) throws Exception {

      FileUtils.resetFile(outFile);
      
      BufferedWriter out = new BufferedWriter(new FileWriter(outFile));
          
      int done = 0;
      
      for (int i = 0; i < data.length;i++) {
    	  out.write(Double.toString(data[i]));
    	  done++;
    	  
    	  if(done < data.length) {
    		  out.newLine();
    	  }
      }
            
      out.close();
  }
    
    /**
     * Write products into files
     * @param outFile
     * @param products
     * @throws Exception
     */
    public void writeDataToFile(String outFile, List <Double> data) throws Exception {

      FileUtils.resetFile(outFile);
      
      BufferedWriter out = new BufferedWriter(new FileWriter(outFile));
          
      int done = 0;
      
      for (int i = 0; i < data.size();i++) {
    	  out.write(Double.toString(data.get(i)));
    	  done++;
    	  
    	  if(done < data.size()) {
    		  out.newLine();
    	  }
      }
            
      out.close();
  }
    
    /**
     * Write data into files
     * @param outFile
     * @param products
     * @throws Exception
     */
    public void writeDataToFile(String outFile, long data) throws Exception {

      FileUtils.resetFile(outFile);
      
      BufferedWriter out = new BufferedWriter(new FileWriter(outFile));
          
      out.write(Long.toString(data));
      
      out.close();

  }
    
    public boolean isValidProduct(Product product, Map<Integer, String> featuresMap, List<Integer> featuresList) throws Exception {
        IVecInt prod = new VecInt(product.size());

        for (Integer s : product) {
        	if (!dimacs) {
	            if (s < 0) {
	                prod.push(-reasonerSAT.getVariableIndex(featuresMap.get(featuresList.get((-s) - 1))));
	            } else {
	                prod.push(reasonerSAT.getVariableIndex(featuresMap.get(featuresList.get(s - 1))));
	            }
        	} else {
        		 prod.push(s);
        	}
        }
        if (!dimacs) {
        	return reasonerSAT.getSolver().isSatisfiable(prod);
        } else {
        	return dimacsSolver.isSatisfiable(prod);
        }
    }

    public boolean isValidProduct(Product product) throws Exception {
        IVecInt prod = new VecInt(product.size());

        for (Integer s : product) {        	
        		 prod.push(s);        	
        }
        
        if (!dimacs) {
        	return reasonerSAT.getSolver().isSatisfiable(prod);
        } else {
        	return dimacsSolver.isSatisfiable(prod);
        }
    }
    
    public boolean isValidPair(TSet pair, Map<Integer, String> featuresMap, List<Integer> featuresList) throws Exception {

        IVecInt prod = new VecInt(pair.getSize()); // Before it is 2, now apply to any t

        for (Integer fi : pair.getVals()) {
            if (!dimacs) {
                if (fi < 0) {
                    prod.push(-reasonerSAT.getVariableIndex(featuresMap.get(featuresList.get((-fi) - 1))));
                } else {
                    prod.push(reasonerSAT.getVariableIndex(featuresMap.get(featuresList.get(fi - 1))));
                }
            } else {
                prod.push(fi);
            }
        }// for 
        
        if (!dimacs) {
            return reasonerSAT.getSolver().isSatisfiable(prod);
        } else {
            return dimacsSolver.isSatisfiable(prod);
        }

    }

    /**     
     * @param products
     * @param n
     * @param t
     * @return
     * @throws Exception
     */
    private Set<TSet> computeNRandValidTSets(List<Product> products, int n, int t) throws Exception {
        Set<TSet> pairs = new HashSet<TSet>(n);
        Random r = new Random();
        while (pairs.size() < n) {
            TSet set = new TSet();
            Product p = products.get(r.nextInt(products.size()));
            List<Integer> prod = new ArrayList<Integer>(p);
            while (set.getSize() < t) {
                set.add(prod.get(r.nextInt(prod.size())));
            }
            pairs.add(set);
        }
        return pairs;
    }

    /**
     * 
     * @param featuresMap
     * @param featuresList
     * @param n
     * @param t
     * @return
     * @throws Exception
     */
    private Set<TSet> computeNRandValidTSets(Map<Integer, String> featuresMap, List<Integer> featuresList, int n, int t) throws Exception {

        Set<TSet> pairs = new HashSet<TSet>(n);

        int size = featuresList.size();
        double total = getBinomCoeff(size, t);
        while (pairs.size() < n) {
            TSet set = getITSet(size, t, Math.floor(Math.random() * total), featuresList);
            if (isValidPair(set, featuresMap, featuresList)) {
                pairs.add(set);
            }
        }

        return pairs;
    }

    private Set<TSet> computeValidPairs(Map<Integer, String> featuresMap, List<Integer> featuresList,
            String outFile, boolean dimacs, ISolver dimacsSolver, int nbParts, int part) throws Exception {


        if (part > nbParts || nbParts < 1) {
            throw new ParameterException("Invalid parts parameters");
        }


        Set<TSet> pairs = new HashSet<TSet>(); //A set of sets


        int size = featuresList.size();

        nCk(size, 2, pairs, featuresMap, featuresList);
        //System.out.println(pairs);
        //System.out.println(pairs.size());
        return pairs;
    }

    private Set<TSet> computeExactValidTSet(Map<Integer, String> featuresMap, List<Integer> featuresList,
            String outFile, boolean dimacs, ISolver dimacsSolver, int t) throws Exception {
    

        Set<TSet> pairs = new HashSet<TSet>(); 


        int size = featuresList.size();

        nCk(size, t, pairs, featuresMap, featuresList);
//        System.out.println(pairs);
        System.out.println("number of valid T-sets " + pairs.size());
        return pairs;
    }
    
    /**
     * 
     * @param outFile
     * @param validTSet
     * @throws Exception
     */
    private void writeValidPairsToFile(String outFile, Set<TSet> validTSet) throws Exception {

        BufferedWriter out = new BufferedWriter(new FileWriter(outFile));       
       
               	
    	for(TSet set:validTSet) { // for each Tset
    		  
    		 int i = 1;
    		 
    		 for (Integer id: set.getVals()) { // for each 
    			 
    			 if (i < set.getVals().size()) {
    				 out.write(Integer.toString(id) + ";");
    			 } else {
    				 out.write(Integer.toString(id));
				 }
				 
				 i++;
				 
    		 }  	
             
             out.newLine();
             
    	}        	        	
   
        out.close();
        
    }
    
    public void computeFeatures(ReasoningWithSAT reasonerSAT, Map<Integer, String> featuresMap, Map<String, Integer> featuresMapRev, List<Integer> featuresList, boolean dimacs, String dimacsFile) throws Exception {

        if (!dimacs) {
            String[] features = reasonerSAT.getVarIndex2NameMap(); // 

            for (int i = 0; i < features.length; i++) {
                String feature = features[i];
                int n = i + 1;
                featuresList.add(n); // ID
                featuresMap.put(n, feature);
                featuresMapRev.put(feature, n);
            }


        } else {
            BufferedReader in = new BufferedReader(new FileReader(dimacsFile));
            String line;
            int n = 0;
            while ((line = in.readLine()) != null && (line.startsWith("c")||line.startsWith("p"))) {
               
            	if (line.startsWith("c")) {
            		 StringTokenizer st = new StringTokenizer(line.trim(), " ");
            		 st.nextToken();
                     n++;
                     String sFeature = st.nextToken().replace('$', ' ').trim(); // 有些特征ID后面加了$，表明该特征名是系统产生的
                     int feature = Integer.parseInt(sFeature);
//                     if (n != feature) { // ID 要按照从小到大的顺序排列
//                         throw new Exception("Incorrect dimacs file, missing feature number " + n + " ?");
//                     }
                     String featureName = st.nextToken();
                     featuresList.add(feature);
                     featuresMap.put(feature, featureName);
                     featuresMapRev.put(featureName, feature);
            	}
            	
            	if (line.startsWith("p")) {
            		 StringTokenizer st = new StringTokenizer(line.trim(), " ");
            		 st.nextToken(); st.nextToken();
            		 numFeatures = Integer.parseInt(st.nextToken());
//            		 System.out.println("numFeatures in computeFeatures " + numFeatures);
            	}
               
            } // while             
            
            in.close();
            
            for (int i = 1;i <= numFeatures;i++) {
            	if (!featuresList.contains(i)) { // 
            		  featuresList.add(i);
                      featuresMap.put(i, Integer.toString(i));
                      featuresMapRev.put(Integer.toString(i), i);
            	}
            }
            
        }

        int n = 1;
        int featuresCount = featuresList.size();
        while (n <= featuresCount) {
            featuresList.add(-n); // 把负ID也加入featureList
            n++;
        }

    }

    /**
     * load constraints 
     * @param reasonerSAT
     * @param featuresMap
     * @param featuresMapRev
     * @param featuresList
     * @param dimacs
     * @param dimacsFile
     * @throws Exception
     */
    public void computeConstraints(ReasoningWithSAT reasonerSAT, boolean dimacs, String dimacsFile) 
    		throws Exception {
    	
//    	  if (!dimacs) {
//              fm = loadFeatureModel(fmFile);
//              fm.loadModel();
//              reasonerSAT = new FMReasoningWithSAT("MiniSAT", fm, SATtimeout);
//              reasonerSAT.init();
//          } else {
//              dimacsSolver = SolverFactory.instance().createSolverByName("MiniSAT");
//              dimacsSolver.setTimeout(SATtimeout);
//
//              DimacsReader dr = new DimacsReader(dimacsSolver);
//              dr.parseInstance(new FileReader(fmFile));
//          }
    	  
    	  
    	if (!dimacs) {   	      

         CNFFormula formula = fm.FM2CNF();
         nConstraints = formula.getClauses().size();
         
         featureModelConstraints = new ArrayList<List<Integer>>(nConstraints);
                  
         
         for (CNFClause clause : formula.getClauses()) {
        	
        	 // 每个字句对应一个 List<Integer> 
             List<Integer> constraint = new ArrayList<Integer>(clause.getLiterals().size());
             
             for (int i = 0; i < clause.getLiterals().size(); i++) { // 子句的每个文字
            	            	 
                 int signal = clause.getLiterals().get(i).isPositive() ? 1 : -1;
                 int varID = reasonerSAT.getVariableIndex(clause.getLiterals().get(i).getVariable().getID());
       
                 if (signal < 0) {
                	 constraint.add(- varID);
                 } else {
                	 constraint.add(varID);
                 }
             } // for i
             
             featureModelConstraints.add(constraint);
         }
         
    	} else { // dimacs形式，则从文件读取约束
        	 
        	 BufferedReader in = new BufferedReader(new FileReader(dimacsFile));
             String line;

             while ((line = in.readLine()) != null) {
                 if (line.startsWith("p")) {
                     StringTokenizer st = new StringTokenizer(line.trim(), " ");
                     st.nextToken();
                     st.nextToken();
                     st.nextToken();
                     nConstraints = Integer.parseInt(st.nextToken());
                     break;

                 }
             }
             
             in.close();

             featureModelConstraints = new ArrayList<List<Integer>>(nConstraints);
             
             // -------------------------------------------------------------
             in = new BufferedReader(new FileReader(dimacsFile));
         
             while ((line = in.readLine()) != null) {
                 if (!line.startsWith("c") && !line.startsWith("p") && !line.isEmpty()) {
                	 List<Integer> constraint = new ArrayList<Integer>();
                     StringTokenizer st = new StringTokenizer(line.trim(), " ");

                     while (st.hasMoreTokens()) {
                         int f = Integer.parseInt(st.nextToken());

                         if (f != 0)  constraint.add(f);   
                     }  
                     
                     featureModelConstraints.add(constraint);  
                 } // if  
                 
             } // while            
             in.close();
             
             //-----------------print 
//             for (int i = 0; i < featureModelConstraints.size();i++) {
//            	 for (int j = 0;j < featureModelConstraints.get(i).size();j++)  {
//            		 System.out.print(featureModelConstraints.get(i).get(j) + " ");
//            	 }
//            	 System.out.println();
//             }
    	}     
             
    } //
    
    
    public void writeCoverageAndFitnessValuesToFile(String outFile, double[] coverageValues, double[] fitnessSums) throws IOException {
        BufferedWriter out = new BufferedWriter(new FileWriter(outFile));
        out.write("#coverage of pairs (in %, starting from 0 products selected);Fitness func");
        out.newLine();
        out.write("0;0");
        out.newLine();
        double s = 0;
        for (int i = 0; i < coverageValues.length; i++) {
            s += coverageValues[i];
            out.write(Double.toString(s) + ";" + Double.toString(fitnessSums[i]));
            out.newLine();
        }
        out.close();
    }

    public void writeRunCoverageToFile(String outFile, double[] coverageValues) throws IOException {
        BufferedWriter out = new BufferedWriter(new FileWriter(outFile));
//        out.write("#coverage of pairs (in %, starting from 0 products selected)");
//        out.newLine();
        out.write("0");
        out.newLine();
        double s = 0;
        for (int i = 0; i < coverageValues.length; i++) {
            s += coverageValues[i];
            out.write(Double.toString(s));
            out.newLine();
        }
        out.close();
    }
    
    public void normalizeDataFile(String inputDir) throws Exception {

        File inDir = new File(inputDir);
        if (!inDir.exists()) {
            throw new ParameterException("Input directory does not exist");
        }

        File[] datFiles = inDir.listFiles(new FilenameFilter() {

            @Override
            public boolean accept(File dir, String name) {
                return name.endsWith(".dat") && !name.toLowerCase().contains("norm");
            }
        });

        for (File file : datFiles) {

            int count = countUncommentedLines(file);

            double[] coverageValues = new double[count];
            double[] fitnessValues = new double[count];

            BufferedReader in = new BufferedReader(new FileReader(file));

            int i = 0;
            String line;

            while ((line = in.readLine()) != null) {
                line = line.trim();
                if (!line.startsWith("#")) {
                    StringTokenizer st = new StringTokenizer(line, ";");

                    coverageValues[i] = Double.parseDouble(st.nextToken().trim());
                    fitnessValues[i] = Double.parseDouble(st.nextToken().trim());
                    i++;
                }
            }
            in.close();

            double[] normalizedCoverageValues = new double[101];
            double[] normalizedFitnessValues = new double[101];

            for (int j = 0; j < normalizedCoverageValues.length; j++) {
                int prodIndex = (int) ((double) j / 100.0 * (coverageValues.length - 1));
                normalizedCoverageValues[j] = coverageValues[prodIndex];
                normalizedFitnessValues[j] = fitnessValues[prodIndex] / fitnessValues[fitnessValues.length - 1] * 100;
            }


            String outFile = file.toString().replace(".dat", "-Norm.dat");
            BufferedWriter out = new BufferedWriter(new FileWriter(outFile));
            out.write("#coverage of pairs (in %, starting from 0% of products selected (normalized));Fitness func (normalized)");
            out.newLine();
            for (int k = 0; k < normalizedCoverageValues.length; k++) {
                out.write(Double.toString(normalizedCoverageValues[k]) + ";" + Double.toString(normalizedFitnessValues[k]));
                out.newLine();
            }
            out.close();
        }

    }

    /**
     * 将vector转换成product，直接vector的元素直接加入product集合即可
     * @param vector
     * @return
     */
    public Product toProduct(int[] vector) {

        Product product = new Product();
        for (int i : vector) {
            product.add(i);
        }
        return product;
    }

    /**
     * 将product转换成IVecInt
     * @param vector
     * @return
     */
    public IVecInt productToIntVec(Product product) {

    	 IVecInt iv = new VecInt();

         for (Integer j: product) {            
             iv.push(j);   
         }
         
        return iv;
    }
    
    /**
     * 将Binary转换成product
     * @param vector
     * @return
     */
    public Product toProduct(Binary bin) {

        Product product = new Product();
        
        for (int i = 0; i < bin.getNumberOfBits();i++) {
        	
        	if (bin.getIth(i) == true){
        		product.add(i + 1);
        	} else {
        		product.add(-(i + 1));
        	}
        		
        } // for i
        return product;
    }
    
    public void computeAverageDataFiles(String inputDir, String outputDir, final boolean noNorm) throws Exception {
        File inDir = new File(inputDir);
        if (!inDir.exists()) {
            throw new ParameterException("Input directory does not exist");
        }

        if (outputDir.equals("Same as input")) {
            outputDir = inputDir;
        }

        if (!new File(outputDir).exists()) {
            throw new ParameterException("Output directory does not exist");
        }
        File[] datFiles = inDir.listFiles(new FilenameFilter() {

            @Override
            public boolean accept(File dir, String name) {
                if (!noNorm) {
                    return name.endsWith("-Norm.dat");
                } else {
                    return name.endsWith(".dat") && !name.toLowerCase().contains("norm");
                }
            }
        });

        Set<String> types = new HashSet<String>();
        for (File file : datFiles) {
            String sFile = file.toString();
            String type = sFile.substring(sFile.lastIndexOf("_") + 1, sFile.length());
            types.add(type);
        }
        for (final String type : types) {
            datFiles = inDir.listFiles(new FilenameFilter() {

                @Override
                public boolean accept(File dir, String name) {
                    return name.endsWith(type);
                }
            });
            int n = 0;
            double[] coverageValues, fitnessValues;
            if (!noNorm) {
                coverageValues = new double[101];
                fitnessValues = new double[101];
            } else {
                int count = minUncommentedLinesCount(datFiles);
                coverageValues = new double[count];
                fitnessValues = new double[count];
            }

            String firstLine = "";
            for (File dat : datFiles) {
                int i = 0;
                BufferedReader in = new BufferedReader(new FileReader(dat));
                String line;
                while ((line = in.readLine()) != null && i < coverageValues.length) {
                    line = line.trim();
                    if (!line.isEmpty()) {
                        if (line.startsWith("#")) {
                            firstLine = line;
                        } else {
                            StringTokenizer tokenizer = new StringTokenizer(line, ";");
                            double cov = Double.parseDouble(tokenizer.nextToken());
                            double fit = Double.parseDouble(tokenizer.nextToken());
                            coverageValues[i] += cov;
                            fitnessValues[i] += fit;
                            i++;
                        }
                    }
                }
                in.close();
                n++;

            }

            for (int i = 0; i < coverageValues.length; i++) {
                coverageValues[i] /= (double) n;
                fitnessValues[i] /= (double) n;
            }

            String outFile = outputDir;
            if (!outFile.endsWith("/")) {
                outFile += "/";
            }
            outFile = outFile + "AVG_ON_ALL_" + type;
            BufferedWriter out = new BufferedWriter(new FileWriter(outFile));

            out.write(firstLine);
            out.newLine();
            for (int i = 0; i < coverageValues.length; i++) {
                out.write(Double.toString(coverageValues[i]) + ";" + Double.toString(fitnessValues[i]));
                out.newLine();
            }
            out.close();
        }
    }

    public int countUncommentedLines(File file) throws Exception {
        BufferedReader in = new BufferedReader(new FileReader(file));
        String line;
        int n = 0;
        while ((line = in.readLine()) != null) {
            line = line.trim();
            if (!line.isEmpty() && !line.startsWith("#")) {
                n++;
            }
        }
        in.close();
        return n;
    }

    public int minUncommentedLinesCount(File[] files) throws Exception {
        int min = countUncommentedLines(files[0]);

        for (int i = 1; i < files.length; i++) {
            int count = countUncommentedLines(files[i]);
            if (count < min) {
                min = count;
            }
        }

        return min;
    }

    public List<Product> loadProductsFromCSVFile(File csvFile, Map<String, Integer> featuresMapRev) throws Exception {
        List<Product> products = new ArrayList<Product>();
        BufferedReader in = new BufferedReader(new FileReader(csvFile));
        String line;
        boolean firstLine = true;
        List<String> features = null;

        if (featuresMapRev != null) {
            features = new ArrayList<String>();
        }
        while ((line = in.readLine()) != null) {
            StringTokenizer tokenizer = new StringTokenizer(line, ";");
            if (firstLine) {
                if (featuresMapRev != null) {
                    while (tokenizer.hasMoreTokens()) {
                        features.add(tokenizer.nextToken().trim());
                    }
                }
                firstLine = false;
            } else {
                Product product = new Product();
                int count;
                if (featuresMapRev != null) {
                    count = 0;
                } else {
                    count = 1;
                }
                while (tokenizer.hasMoreTokens()) {
                    String tok = tokenizer.nextToken().trim();
                    if (tok.equals("X")) {
                        if (featuresMapRev != null) {
                            product.add(featuresMapRev.get(features.get(count)));
                        } else {
                            product.add(count);
                        }
                    } else if (tokenizer.equals("-")) {
                        if (featuresMapRev != null) {
                            product.add(-featuresMapRev.get(features.get(count)));
                        } else {
                            product.add(-count);
                        }
                    }
                    count++;

                }
                products.add(product);
            }
        }
        return products;
    }

    public double[] computeFitnessSums(List<Product> products, int distanceMethod) {
        int size = products.size();

        double[][] distancesMatrix = new double[size][size];

        for (int i = 0; i < size; i++) {
            for (int j = 0; j < size; j++) {
                if (j > i) {
                    distancesMatrix[i][j] = DistancesUtil.getJaccardDistance(products.get(i), products.get(j));
                }
            }
        }
        double[] fitnessSums = new double[size];
        int n = size - 1;

        while (n >= 0) {
            fitnessSums[n] = SimilarityTechnique.getJaccardFitnessSum(distancesMatrix, n + 1);
            n--;
        }
        return fitnessSums;
    }

    public void computeValidPairsToFile(String fmFile, boolean dimacs, int nbParts, int part) throws Exception {

        if (!new File(fmFile).exists()) {
            throw new ParameterException("The specified FM file does not exist");
        }


        int timeoutS = 300;
        List<Integer> featuresList = new ArrayList<Integer>();
        Map<Integer, String> featuresMap = new HashMap<Integer, String>();
        Map<String, Integer> featuresMapRev = new HashMap<String, Integer>();
        if (!dimacs) {

            fm = loadFeatureModel(fmFile);
            fm.loadModel();
            reasonerSAT = new FMReasoningWithSAT("MiniSAT", fm, timeoutS);
            reasonerSAT.init();
            reasonerSAT.getSolver().setTimeout(timeoutS);


            computeFeatures(reasonerSAT, featuresMap, featuresMapRev, featuresList, false, null);

            computeValidPairs(featuresMap, featuresList, (fmFile + ".validpairs"), false, null, nbParts, part);
        } else {
            computeFeatures(null, featuresMap, featuresMapRev, featuresList, true, fmFile);
            dimacsSolver = SolverFactory.instance().createSolverByName("MiniSAT");
            dimacsSolver.setTimeout(timeoutS);
            DimacsReader dr = new DimacsReader(dimacsSolver);
            dr.parseInstance(new FileReader(fmFile));
            computeValidPairs(featuresMap, featuresList, (fmFile + ".validpairs"), true, dimacsSolver, nbParts, part);
        }
    }

    public Set<TSet> loadPairs(String pairsFile) throws Exception {
        if (!new File(pairsFile).exists()) {
            throw new ParameterException("The specified FM file does not exist");
        }

        LineNumberReader lnr = new LineNumberReader(new FileReader(pairsFile));
        lnr.skip(Long.MAX_VALUE);

        List<TSet> pairs = new ArrayList<TSet>(lnr.getLineNumber());

        BufferedReader in = new BufferedReader(new FileReader(pairsFile));
        String line;

        while ((line = in.readLine()) != null) {
            if (!line.isEmpty()) {
                StringTokenizer st = new StringTokenizer(line, ";");

                TSet pair = new TSet();
                pair.add(Integer.parseInt(st.nextToken()));
                pair.add(Integer.parseInt(st.nextToken()));
                pairs.add(pair);
            }
        }

        in.close();

        Set<TSet> pairsSet = new HashSet<TSet>(pairs);
        return pairsSet;

    }

    public Set<TSet> loadValidTSet(String validFile) throws Exception {
        if (!new File(validFile).exists()) {
            throw new ParameterException("The specified valid file does not exist");
        }

        LineNumberReader lnr = new LineNumberReader(new FileReader(validFile));
        lnr.skip(Long.MAX_VALUE);

        List<TSet> tset = new ArrayList<TSet>(lnr.getLineNumber());

        BufferedReader in = new BufferedReader(new FileReader(validFile));
        String line;

        while ((line = in.readLine()) != null) {
            if (!line.isEmpty()) {
                StringTokenizer st = new StringTokenizer(line, ";");

                TSet set = new TSet();
                
                while (st.hasMoreTokens()) {
	                set.add(Integer.parseInt(st.nextToken()));	               
                }
                
                tset.add(set);
            }//if
        }

        in.close();

        Set<TSet> validTSet = new HashSet<TSet>(tset);
        return validTSet;
    }
    
    /**
     * Load mandatory and dead indices from files
     * @param mandatory
     * @param dead
     * @throws Exception
     */
    public void loadMandatoryDeadFeaturesIndices(String mandatory, String dead) throws Exception {

        mandatoryFeaturesIndices = new ArrayList<Integer>(numFeatures);
        deadFeaturesIndices = new ArrayList<Integer>(numFeatures);
        featureIndicesAllowedFlip = new ArrayList<Integer>(numFeatures);               

        File file = new File(mandatory);   
        
        if (file.exists()) {      
        
	        BufferedReader in = new BufferedReader(new FileReader(mandatory));
	        String line;
	        while ((line = in.readLine()) != null) {
	            if (!line.isEmpty()) {
	                int i = Integer.parseInt(line) - 1;
	                mandatoryFeaturesIndices.add(i);	               
	            }
	
	        }
	        
	        in.close();
        } 
        
        file = new File(dead);   
        
        if (file.exists()) {           	
        
	        BufferedReader  in = new BufferedReader(new FileReader(dead));
	        String line;
	        while ((line = in.readLine()) != null) {
	            if (!line.isEmpty()) {
	                int i = Integer.parseInt(line) - 1;
	                deadFeaturesIndices.add(i);	        
	            }
	
	        }
	        
	        in.close();
        } // if 
        
         for (int i = 0; i < numFeatures; i++) {
            if (! mandatoryFeaturesIndices.contains(i) && !deadFeaturesIndices.contains(i))
                featureIndicesAllowedFlip.add(i);
            
        }

         System.out.println("mandatoryFeaturesIndices.size() = " + mandatoryFeaturesIndices.size());
         System.out.println("deadFeaturesIndices.size() = " + deadFeaturesIndices.size());
//         System.out.println("featureIndicesAllowedFlip.size() = " + featureIndicesAllowedFlip.size());
         
    }
       

    /**
     * 初始化模型及求解器
     * @param fmFile
     * @param nbPairs
     * @param t
     * @throws Exception
     */
    public void initializeModelSolvers(String fmFile, int t) throws Exception {
 
        if (!new File(fmFile).exists()) {
            throw new ParameterException("The specified FM file does not exist");
        }

        this.predictable = false;// 
        this.dimacs = true; //
        this.dimacsFile = fmFile;// 
        
        //System.out.println("--------------Initialize SAT solvers-------------");
        /**
         * ---------------------Initialize SAT4J solvers--------------------------------
         */
        dimacsSolver = SolverFactory.instance().createSolverByName("MiniSAT");
        dimacsSolver.setTimeout(SATtimeout);

        DimacsReader dr = new DimacsReader(dimacsSolver);
        dr.parseInstance(new FileReader(fmFile));
        
    	if (!predictable) {
    		((Solver) dimacsSolver).setOrder(order);
    	}
    	
//        solverIterator = new ModelIterator(dimacsSolver);
        solverIterator =  dimacsSolver; 
        solverIterator.setTimeoutMs(iteratorTimeout);
        // ---------------------Initialize SAT4J solvers（End）-------------------------------
         
        //System.out.println("--------------读取特征、约束及core、dead features-------------");
        /**
         * ---------------------Load features, constraints, core and dead features---------------------
         */
        featuresList   = new ArrayList<Integer>();
        featuresMap    = new HashMap<Integer, String>(); 
        featuresMapRev = new HashMap<String, Integer>(); 
       
        computeFeatures(null, featuresMap, featuresMapRev, featuresList, true, fmFile);
        computeConstraints(null, true, fmFile);               
        
        System.out.println("numFeatures"  + numFeatures);
        System.out.println("numConstraints"  + nConstraints);
        
        //Read indexes for mandatory and dead features (= ID-1)
        loadMandatoryDeadFeaturesIndices(fmFile+".mandatory", fmFile+".dead");
        // ---------------------Load features, constraints, core and dead features (end)--------------------
             
        // Initialize probSAT solver      
        HashMap  localSearchParameters ;     
        localSearchParameters = new HashMap() ;
        localSearchParameters.put("constraints",featureModelConstraints); //featureModelConstraints 在computeConstraints中读取了
        localSearchParameters.put("num_vars",numFeatures); 
        localSearchParameters.put("max_flips",8000);
        localSearchParameters.put("wp", 0.567);

        repairSolver = new ProbSATLocalSearch(localSearchParameters);// ProbSAT                    
           
        // Read T-set            
        //System.out.println("--------------load T-set-------------");
        String validTsetFile = fmFile + ".valid" + t + "-Set"  ;    	     
    
        if (validTsetFile != null && (new File(validTsetFile).exists())) {
        	
//        	System.out.println(validTsetFile);
        	validTSets = loadValidTSet(validTsetFile);  
        	System.out.println("Number of validTSets " + validTSets.size());
        	
        } else {
        	
        	System.out.println("---------Generate validTSets------------");
        	
            if (t == 2 && numFeatures <= 1000)  {
        		validTSets = computeExactValidTSet(featuresMap, featuresList, null, false, null, t);// 精确算法
        	} else {
        		
        		int  nbPairs;        		
    			         		
           		nbPairs = t * 25000; // Any number you prefer. 
        		
        		System.out.println("Number of valid sets to be generated " + nbPairs);
        		
        		validTSets = computeNRandValidTSets(featuresMap, featuresList, nbPairs, t);
        	}
        		
        	writeValidPairsToFile(validTsetFile, validTSets);
        	
        }  // IF  

        System.out.println("-------------initializeModelSolvers end-------------");
    } // end of class
    
    /**
     * 
     * @param fmFile
     * @param outputDir
     * @param runs
     * @param dimacs
     * @param nbPairs
     * @param t
     * @param nbProds
     * @param timeAllowed
     * @throws Exception
     */
    public void samplingProductsSAT4JUnpredictable(String fmFile,String outputDir, int runs,int nbProds,int t, long timeAllowed) throws Exception {
   

        String sNbProds = "" + nbProds;
        String fmFileName = new File(fmFile).getName();

        System.out.println("Start samplingProductsSAT4JUnpredictable...");
       
        double avgCoverage = 0.0;
        double avgFitness = 0.0;
        //SimilarityTechnique st = new SimilarityTechnique(SimilarityTechnique.JACCARD_DISTANCE, SimilarityTechnique.NEAR_OPTIMAL_SEARCH);
        
        String path = outputDir + "SAT4JUnpredictable/" + fmFileName + "/Samples/" + sNbProds + "prods/"+ timeAllowed + "ms/"; // 单独 存储Samples   
        FileUtils.CheckDir(path); 
        
        String tCoveragePath = outputDir + "SAT4JUnpredictable/" + fmFileName +"/" + t + "wise/" + sNbProds + "prods/"+ timeAllowed + "ms/";       
        FileUtils.CheckDir(tCoveragePath); 
        
        for (int i = 0; i < runs; i++) {
            System.out.println("run " + (i + 1));        	
            List<Product> products = null; //
            
            // Use the unpredictable way to  generate products			
			long startTimeMS = System.currentTimeMillis();
			
			products = getUnpredictableProducts(nbProds); 
			//shuffle(products); //
			
			long endTimeMS = System.currentTimeMillis() - startTimeMS;
			
			// Save products
			writeProductsToFile(path + "Products." + i, products);
			// Save runtime
		    writeDataToFile(path + "RUNTIME." + i, endTimeMS);// write RUNTIME
		      
	     
           computeProductsPartialCoverage(products, validTSets);                     
           
    	   double [] runCoverage= new double[nbProds];
           double sumCoverageValues = 0.0;
           
           for (int j = 0; j < nbProds; j++) {
               double cov = products.get(j).getCoverage();
               sumCoverageValues += cov; // Cumulative coverage
               runCoverage[j] = cov;   
           }
           
           System.out.println("t = " + t + " Coverage = " + sumCoverageValues);           
           
           writeDataToFile(tCoveragePath + "Coverage." + i, sumCoverageValues);// write coverage
           writeRunCoverageToFile(tCoveragePath + "RunCoverage." + i, runCoverage);// write RUNcoverage            
           
        } // for runs      

    }
    
    
    /**
     * 探究order如何影响均匀性
     * @param fmFile
     * @param outputDir
     * @param runs
     * @param dimacs
     * @param nbPairs
     * @param t
     * @param nbProds
     * @param timeAllowed
     * @throws Exception
     */
    public void samplingProductsSAT4JUnpredictableOrder(String fmFile,String outputDir, int runs,int t,int nbProds,long timeAllowed) throws Exception {
   

        String sNbProds = "" + nbProds;
        String fmFileName = new File(fmFile).getName();

      System.out.println("Start samplingProductsSAT4JUnpredictableOrder...");
       
        double avgCoverage = 0.0;
        double avgFitness = 0.0;
        SimilarityTechnique st = new SimilarityTechnique(SimilarityTechnique.JACCARD_DISTANCE, SimilarityTechnique.NEAR_OPTIMAL_SEARCH);
        
        String path = outputDir + "SAT4JUnpredictableOrder/" + fmFileName +"/" + t + "wise/" + sNbProds + "prods/"+ timeAllowed + "ms/";
        FileUtils.CheckDir(path); 
        
        for (int i = 0; i < runs; i++) {
//          System.out.println("run " + (i + 1));
        	
            List<Product> products = null; //
            double [] runCoverage= new double[nbProds];
            double sumCoverageValues = 0.0;
            
            /*
             * 采用随机化的SAT4J生成一组随机解
             */
            long startTimeMS = System.currentTimeMillis();
            
            products = getUnpredictableProductsSetOrderDuringRun(nbProds); 
//	        shuffle(products); // 洗牌
            
            long endTimeMS = System.currentTimeMillis() - startTimeMS;
	        /*
	         * 计算覆盖率
	         */
            computeProductsPartialCoverage(products, validTSets);   // 部分覆盖率                           
//            computeProductsCoverage(products, validTSets);  
            
            for (int j = 0; j < nbProds; j++) {
                double cov = products.get(j).getCoverage();
                sumCoverageValues += cov; //累积覆盖率
                runCoverage[j] = cov;    //当前product的覆盖率
            }
            
//            System.out.println("Unpredictable的累积覆盖率=" + sumCoverageValues);            
            
            /*
             * --------------------计算适应度值------------------------------------
             */
//            products = st.prioritize(products);
//            double fitness = st.getLastFitnessComputed();
//              double fitness = st.PD(products);
              double fitness = st.noveltyScoreSum(products, 20);
            
//            double[] fitness = null;
//            double sumfitnessValue = 0.0; 
//            
//            fitness = computeFitnessSums(products, SimilarityTechnique.JACCARD_DISTANCE);
//            
//            for (int j = 0; j < fitness.length; j++) {
//            	sumfitnessValue += fitness[j]; // 累积适应度
//            }
                        
//            System.out.println("Unpredictable的累积适应值=" + fitness);                                            
                  
            avgCoverage = avgCoverage + sumCoverageValues;    
            avgFitness = avgFitness + fitness;
            
            //Save products           
            writeProductsToFile(path + "Products." + i, products);
            writeDataToFile(path + "Coverage." + i, sumCoverageValues);// write coverage
            writeRunCoverageToFile(path + "RunCoverage." + i, runCoverage);// write coverage
            writeDataToFile(path + "Fitness." + i, fitness);// write PD
            writeDataToFile(path + "RUNTIME." + i, endTimeMS);// write coverage
        } // for runs
        
        avgCoverage = avgCoverage / runs;        
        avgFitness  = avgFitness / runs;        
        System.out.println("Unpredictable avgCoverage = " + avgCoverage);
        System.out.println("Unpredictable avgFitness = " + avgFitness);
        writeDataToFile(path + "Coverage.avg", avgCoverage);// write coverage
        writeDataToFile(path + "PD.avg", avgFitness);// write coverage
    }
    
        
    /**
     * 
     * @param fmFile
     * @param outputDir
     * @param runs
     * @param dimacs
     * @param nbPairs
     * @param t
     * @param nbProds
     * @param timeAllowed
     * @throws Exception
     */
    public void samplingDownProductsR1(String fmFile,String outputDir, int runs,int t,int nbProds,long timeAllowed) throws Exception {   

        String sNbProds = "" + nbProds;
        String fmFileName = new File(fmFile).getName();

        System.out.println("Start samplingDownR1..");
       
        double avgCoverage = 0.0;          
        
        // Path to save products
        String path = outputDir +  "SamplingDown/" + fmFileName +"/Samples/" + sNbProds + "prods/"+ timeAllowed + "ms/";
        FileUtils.CheckDir(path); 
        
        // Path to save t-wise coverage
        String twisePath = outputDir +  "SamplingDown/" + fmFileName +"/" + t + "wise/" + sNbProds + "prods/"+ timeAllowed + "ms/";
        FileUtils.CheckDir(twisePath); 
        
        
        for (int i = 0; i < runs; i++) {
            System.out.println("run SamplingDownR1:" + (i + 1));
        	
            List<Product> products = new ArrayList<Product>();
            
            double [] runCoverage= new double[nbProds];
            double sumCoverageValues = 0.0;

            long startTimeMS = System.currentTimeMillis();
            
            int number = 0;            
                    
            //-------------------Method 1-----------------------
//            int sampleSize = 1000;    
//            if (numFeatures >=500 && numFeatures <=1000) 
//            	sampleSize = 800;
//            else if (numFeatures > 1000 && numFeatures < 10000) 
//            	sampleSize = 500; //
//            else if (numFeatures > 10000)  {
//            	sampleSize = 200; //
//            }
            //-------------------Method 1 end -----------------------
            
            
            //----------------------Method 2------------------------
            double [][] temp =  FileUtils.readMatrix(outputDir +  "NS/" + fmFileName +"/Samples/" + sNbProds + "prods/"+ timeAllowed + "ms/Evaluations."+i);
            int sampleSize  = (int)(temp[0][0]/2);
            if(sampleSize > 10000) sampleSize = 10000;
            System.out.println("sampleSize = " + sampleSize);            
            //----------------------Method 2 (end)-------------------
            
            
            while ( products.size() < sampleSize) { 
            	Product prod = getUnpredictableProduct();
            	if (!products.contains(prod)) {
            		products.add(prod);
            		number++;
            	}
            }
            
            System.out.println("Actually generated samples = " + number);
         
            // ------------------------Sampling down---------------------------------
            List<Product> productsCopy = new ArrayList<Product>(products);
            products.clear();
            
            List<Integer> addedProductIndex = new ArrayList<Integer>(nbProds);
            boolean [] ifRemoved = new boolean[productsCopy.size()];
            
            // Construct distance matrix
            double [] [] AllDistances = new double [productsCopy.size()][productsCopy.size()]; 
            
            for (int k=0;k<productsCopy.size();k++) {
            	
            	for (int j=k+1;j<productsCopy.size();j++) {
            		AllDistances[k][j] = DistancesUtil.getHammingDistance(productsCopy.get(k), productsCopy.get(j));
            		AllDistances[j][k] = AllDistances[k][j];
            	}
            }
            
           // find all-ones products  
            int maxSelected = -1;
            int maxSelectedIdx = -1;
            
            for (int j = 0; j < productsCopy.size();j++) {
            	int selectedNumber = productsCopy.get(j).getSelectedNumber();
            	
            	if (selectedNumber > maxSelected) {
            		maxSelected = selectedNumber;
            		maxSelectedIdx = j;
            	}
            	
            }
            
            ifRemoved[maxSelectedIdx] = true;            
            addedProductIndex.add(maxSelectedIdx);
                   
                   
            while (addedProductIndex.size() < nbProds) {
            	
            	double maxMinDist = Double.MIN_VALUE;
            	int maxMinDistID = -1;
            	
            	
            	for (int m = 0; m < productsCopy.size();m++) {
            		
            		if (ifRemoved[m] == false) {
            			
	            		double minDist = Double.MAX_VALUE;
	            		
	            		for (int n = 0; n < addedProductIndex.size();n++) {
	            			double dist = AllDistances[m][addedProductIndex.get(n)]; 
	            			
	            			if (dist == 0.0) {
	            				System.out.println("Error in distance of samplingDownProductsR1");
	            			}
	            				            			
	            			if (dist < minDist) {
	            				minDist = dist;
	            			}
	            		} // for n
	            		
	            		
	            		if (minDist > maxMinDist) {
	            			maxMinDist = minDist;
	            			maxMinDistID = m;
	            		}
	            		
            		} // if 
            		
            	} // for m            	
          
            	addedProductIndex.add(maxMinDistID);
            	ifRemoved[maxMinDistID] = true;
                
            } // while
            
            
            for (int k = 0; k < nbProds;k++) {
            	products.add(productsCopy.get(addedProductIndex.get(k)));
            }
                       
            
            long endTimeMS = System.currentTimeMillis() - startTimeMS;
            System.out.println("Sample down total runtime " + endTimeMS);
	
            // Write  products and runtime
            writeProductsToFile(path + "Products." + i, products);
            writeDataToFile(path + "RUNTIME." + i, endTimeMS);// write runtime

                        
            computeProductsPartialCoverage(products, validTSets);   // 部分覆盖率                           
            
            for (int j = 0; j < nbProds; j++) {
                double cov = products.get(j).getCoverage();
                sumCoverageValues += cov; //累积覆盖率
                runCoverage[j] = cov;    //当前product的覆盖率
            }
            
            System.out.println("samplingDownR1's " + t +"-wise coverage = " + sumCoverageValues);    
            
            avgCoverage = avgCoverage + sumCoverageValues;    
                                 
            writeDataToFile(twisePath + "Coverage." + i, sumCoverageValues);// write coverage
            writeRunCoverageToFile(twisePath + "RunCoverage." + i, runCoverage);// write Run coverage

        } // for runs        
            
        avgCoverage = avgCoverage / runs;           
        System.out.println("samplingDownR1's" + " avgCoverage = " + avgCoverage);
        writeDataToFile(twisePath + "Coverage.avg", avgCoverage);// write average coverage

    }
    
    
    
    /**
     * 
     * @param fmFile
     * @param outputDir
     * @param runs
     * @param dimacs
     * @param nbPairs
     * @param t
     * @param nbProds
     * @param timeAllowed
     * @throws Exception
     */
    public void fitnessRelateCoverage(String fmFile,String outputDir, int runs,int t,int nbProds) throws Exception {
   
        String sNbProds = "" + nbProds;
        String fmFileName = new File(fmFile).getName();
       
        double avgCoverage = 0.0;
        double avgFitness = 0.0;
        SimilarityTechnique st = new SimilarityTechnique(SimilarityTechnique.JACCARD_DISTANCE, SimilarityTechnique.NEAR_OPTIMAL_SEARCH);
        
        double [] coverage = new double [runs];
        double [] fitnessSimilarity = new double [runs];
        double [] fitnessNovelty = new double [runs]; // Nb = 15
        double [] fitnessNoveltyNb2 = new double [runs]; // Nb = 2
        double [] fitnessNoveltyNbQuarterSampleSize = new double [runs]; // Nb = quarter SampleSize 
        double [] fitnessNoveltyNbHalfSampleSize = new double [runs]; // Nb = Half SampleSize 
        double [] fitnessNoveltyNbThreeQuarterSampleSize = new double [runs]; // Nb = three quarter SampleSize 
        
        //double [] fitnessPD = new double [runs];
        
        String path = outputDir + "RelationNS2Coverage/SampleResults/" + fmFileName +"/" + sNbProds + "prods/";
        FileUtils.CheckDir(path); 
        
        
        for (int i = 0; i < runs; i++) {
//          System.out.println("run " + (i + 1));
        	
            List<Product> products = null; //           
                       
            if (!(new File(path + "Products." + i)).exists()) { 
            	products = getUnpredictableProductsSetOrderDuringRun(nbProds); 
//            	products = getUnpredictableProducts(nbProds); 
            	System.out.println("Sampling");
                writeProductsToFile(path + "Products." + i, products);
                
            } else {
            	 products = loadProductsFromFile(path + "Products." + i);
            	 System.out.println("Reading " + i);
            }            
            
	        /*
	         * Calculate coverage
	         */
            computeProductsPartialCoverage(products, validTSets);                     
//            computeProductsCoverage(products, validTSets);  
            
            coverage[i] = 0;
            for (int j = 0; j < nbProds; j++) {
                double cov = products.get(j).getCoverage();
                coverage[i] += cov; 
            }
                   
            /*
             * --------------------Calculate novelty scores-----------------------------------
             */
            products = st.prioritize(products);            
            fitnessSimilarity[i] = st.getLastFitnessComputed();    //  Similarity-based fitness        
           
            double [][] distance = new double [nbProds][nbProds];
            distance = st.calculateDistanceMatrix(products);
            
            fitnessNovelty[i] = st.noveltyScoreSum(distance, 15); // Novelty-based fitness Nb = 15
            fitnessNoveltyNb2[i] = st.noveltyScoreSum(distance, 2); // Novelty-based fitness Nb = 2
            fitnessNoveltyNbQuarterSampleSize[i] = st.noveltyScoreSum(distance, (int)(nbProds/4.0)); // Novelty-based fitness Nb = SampleSize/4
            fitnessNoveltyNbHalfSampleSize[i] = st.noveltyScoreSum(distance, (int)(nbProds/2.0)); // Novelty-based fitness Nb = SampleSize/2
            fitnessNoveltyNbThreeQuarterSampleSize[i] = st.noveltyScoreSum(distance, (int)(3*nbProds/4.0)); // Novelty-based fitness Nb = 3/4 * SampleSize          
            //fitnessSimilarity[i] = st.noveltyScoreSum(distance, nbProds);   //  Nb =  SampleSize, i.e., Similarity-based fitness  
        } // for runs
        
        double [][] data = new double [runs][7];
        
        for (int i = 0; i < runs;i++) {
        	data[i][0] = coverage[i];
        	data[i][1] = fitnessSimilarity[i];
        	data[i][2] = fitnessNovelty[i]; //15
        	data[i][3] = fitnessNoveltyNb2[i]; 
        	data[i][4] = fitnessNoveltyNbQuarterSampleSize[i];        	
        	data[i][5] = fitnessNoveltyNbHalfSampleSize[i];
        	data[i][6] = fitnessNoveltyNbThreeQuarterSampleSize[i];    
        }
        		        
        FileUtils.CheckDir(outputDir + "RelationNS2Coverage/");     
        
        String mPath = outputDir + "RelationNS2Coverage/" +  t + "wise/" + sNbProds + "prods/Sampling" + runs + "Times/";
        FileUtils.CheckDir(mPath); 
        mPath = mPath + "FM_" + fmFileName + ".m";
        FileUtils.writeMatrix(mPath, data,true);

    }
    
    public void fitnessRelateCoverageAppend(String fmFile,String outputDir, int runs,int t,int nbProds) throws Exception {
    	   
        String sNbProds = "" + nbProds;
        String fmFileName = new File(fmFile).getName();
       
        double avgCoverage = 0.0;
        double avgFitness = 0.0;
        SimilarityTechnique st = new SimilarityTechnique(SimilarityTechnique.JACCARD_DISTANCE, SimilarityTechnique.NEAR_OPTIMAL_SEARCH);
        
        double [] fitnessSimilarity = new double [runs];

        
        //double [] fitnessPD = new double [runs];
        
        String path = outputDir + "RelationFitnessCoverageR1/SampleResults/" + fmFileName +"/" + sNbProds + "prods/";
        FileUtils.CheckDir(path); 
        
        
        for (int i = 0; i < runs; i++) {
          System.out.println("run " + (i + 1));
        	
            List<Product> products = null; //

            
            if (!(new File(path + "Products." + i)).exists()) { // 若不存在，则产生
            	products = getUnpredictableProductsSetOrderDuringRun(nbProds); 
//            	products = getUnpredictableProducts(nbProds); 
            	System.out.println("Sampling");
                writeProductsToFile(path + "Products." + i, products);
                
            } else {
            	 products = loadProductsFromFile(path + "Products." + i);
            	 System.out.println("Reading " + i);
            }            
   
            
            /*
             * --------------------计算适应度值------------------------------------
             */
            products = st.prioritize(products);            
            fitnessSimilarity[i] = st.getLastFitnessComputed();    //  Similarity-based fitness        
           
        } // for runs
        
        double [][] data = new double [runs][1];
        
        for (int i = 0; i < runs;i++) {       
        	data[i][0] = fitnessSimilarity[i];
        }
        		        
        FileUtils.CheckDir(outputDir + "RelationFitnessCoverageR1/");     
        
        String mPath = outputDir + "RelationFitnessCoverageR1/" +  t + "wise/" + sNbProds + "prods/Sampling" + runs + "Times/";
        FileUtils.CheckDir(mPath); 
        mPath = mPath + "FM_" + fmFileName + ".m";
        FileUtils.writeMatrix2Existing(mPath, data,true);        
    }   
   
   
}
