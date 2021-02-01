/* GenerateFromExistingResultsMain.java
 * 
 * For different t, we can generate t-wise coverage from sampled results.
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
 * You should have received a copy of the GNU  General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 * 
 */
package spl;

import java.io.File;
import java.util.List;
import java.util.Set;

import spl.fm.Product;
import spl.fm.TSet;
import spl.techniques.SimilarityTechnique;
import spl.utils.FileUtils;


public class GenerateFromExistingResultsMain {

	public int exisitingT = 2;
	public int nbProds = 100;
	public int t = 6;
	public long timeAllowed; 
	public String outputDir;
	public int runs;
	public String algName;
	private Set<TSet> validTSets;
	 
	public GenerateFromExistingResultsMain() {
		
	}
	

	public void loadTSets(String fmFile) throws Exception {
		 /**
         * 读取T-set
         */        
        String validTsetFile = "./all_FM/"  + fmFile + ".valid" + t + "-Set_" + nbProds + "products";    	    
    
        if (validTsetFile != null && (new File(validTsetFile).exists())) {       	

        	validTSets = SPL.getInstance().loadValidTSet(validTsetFile);    
//        	System.out.println("Number of validTSets " + validTSets.size());
        	
        }

	}
	
	
	public void computeTwiseCoverage(String fmFile) throws Exception{
		 String sNbProds = "" + nbProds;
         String fmFileName = new File(fmFile).getName();

        
         double avgCoverage = 0.0;
         //double avgFitness = 0.0;
         SimilarityTechnique st = new SimilarityTechnique(SimilarityTechnique.JACCARD_DISTANCE, SimilarityTechnique.NEAR_OPTIMAL_SEARCH);
                         
         String path = outputDir + algName  + "/" + fmFileName +"/" + t + "wise/" + sNbProds + "prods/"+ timeAllowed + "ms/";
         FileUtils.CheckDir(path); 
         
         String loadProductsPath = outputDir + algName  + "/"  + fmFileName + "/Samples/" + sNbProds + "prods/"+ timeAllowed + "ms/";            
         
         for (int i = 0; i < runs; i++) {
             System.out.println("ComputeTwiseCoverage, run " + (i + 1));
         	
             List<Product> products = null; //
             double [] runCoverage= new double[nbProds];
             double sumCoverageValues = 0.0;
             
             // Load products                            
             products = SPL.getInstance().loadProductsFromFile(loadProductsPath + "Products." + i);
// 	         shuffle(products); // 洗牌
 	                      
             /*
 	         * 计算覆盖率
 	         */
             SPL.getInstance().computeProductsPartialCoverage(products, SPL.getInstance().validTSets);                              
           
             for (int j = 0; j < nbProds; j++) {
                 double cov = products.get(j).getCoverage();
                 sumCoverageValues += cov; //累积覆盖率
                 runCoverage[j] = cov;    //当前product的覆盖率
             }
             
//             System.out.println("NS的累积覆盖率=" + sumCoverageValues);            
             
             /*
              * 计算适应度值
              */
//           products = st.prioritize(products);
//           double fitness = st.getLastFitnessComputed();
//             double fitness = st.PD(products);
//             double fitness = st.noveltyScoreSum(products, nbProds/2);                                                     
                   
             avgCoverage = avgCoverage + sumCoverageValues;    
//             avgFitness = avgFitness + fitness;
             
             System.out.println("t = " + t + " Coverage = " + sumCoverageValues);                
       

             SPL.getInstance().writeDataToFile(path + "Coverage." + i, sumCoverageValues);// write coverage
             SPL.getInstance().writeRunCoverageToFile(path + "RunCoverage." + i, runCoverage);// write coverage
//             SPL.getInstance().writeDataToFile(path + "Fitness." + i, fitness);// write Novelty score        

         } // for runs   
         
	}
	
	public void computeFitness(String fmFile) throws Exception{
		 String sNbProds = "" + nbProds;
        String fmFileName = new File(fmFile).getName();

       
        double avgCoverage = 0.0;
        //double avgFitness = 0.0;
        SimilarityTechnique st = new SimilarityTechnique(SimilarityTechnique.Anti_Dice_Distance, SimilarityTechnique.NEAR_OPTIMAL_SEARCH);
                        
        String path = outputDir + algName  + "/" + fmFileName + "/Samples/" + sNbProds + "prods/"+ timeAllowed + "ms/";
        FileUtils.CheckDir(path); 
        
        String loadProductsPath = outputDir + algName  + "/"  + fmFileName + "/Samples/" + sNbProds + "prods/"+ timeAllowed + "ms/";            
        
        for (int i = 0; i < runs; i++) {
            System.out.println("computeFitness, run " + (i + 1));
        	
            List<Product> products = null; //
            
            // Load products                            
            products = SPL.getInstance().loadProductsFromFile(loadProductsPath + "Products." + i);
//	         shuffle(products); // 洗牌
	                      
            /*
             * 计算适应度值
             */
//          products = st.prioritize(products);
//          double fitness = st.getLastFitnessComputed();
//            double fitness = st.PD(products);
            double fitness = st.noveltyScoreSum(products, nbProds/2);                                                     

            SPL.getInstance().writeDataToFile(path + "Fitness." + i, fitness);// write Novelty score        

        } // for runs   
        
	}
	
	public void computeFaultRate(String fmFile) throws Exception{
		String sNbProds = "" + nbProds;
        String fmFileName = new File(fmFile).getName();
                  
        // Write path for faults
        String path =  outputDir + algName  + "/" + fmFileName +"/" + t + "wise/" + sNbProds + "prods/"+ timeAllowed + "ms/";
        FileUtils.CheckDir(path); 
        
        // Load path for products 
        String loadProductsPath = outputDir + algName  + "/" + fmFileName +"/Samples/"  + sNbProds + "prods/"+ timeAllowed + "ms/";
       		 
        // Load path for faults
        String faultsDir = "./all_FM/TSE/" + fmFileName + ".faults/";      
        
        int repeatTimes = 100;        
        
        for (int i = 0; i < runs; i++) {
//          System.out.println("run " + (i + 1));
        	
            List<Product> products = null; 
            // Load products                            
            products = SPL.getInstance().loadProductsFromFile(loadProductsPath + "Products." + i);
	                  
            double sumFaultsValues = 0.0;               
            double [] faults = new double[repeatTimes];
            
            
            for (int k = 0; k < repeatTimes;k++) {
            	
            	 String faultsFile = faultsDir + "faults." + k;    	
            	 
                 if (faultsFile != null && (new File(faultsFile).exists())) {
                 	           
                 	validTSets = SPL.getInstance().loadValidTSet(faultsFile);   
//                 	System.out.println("Loading faults. Number of faults " + validTSets.size());
                 	
                 	SPL.getInstance().computeProductsPartialFaults(products, validTSets);  
                 	
                 	double faultsRate = 0.0;
                    for (int j = 0; j < nbProds; j++) {
                        double coverFaults = products.get(j).getCoverage();
                        faultsRate += coverFaults; //累积错误数       
                    }
                    
                    faults[k] = faultsRate/validTSets.size() * 100;                      
                    sumFaultsValues = sumFaultsValues + faultsRate/validTSets.size() * 100;                    
                 } // IF    
                 
             }  // for k               
                                                     
            sumFaultsValues = sumFaultsValues/repeatTimes;     

            SPL.getInstance().writeDataToFile(path + "MeanFaultRate." + i, sumFaultsValues);// write mean faults rate  
            SPL.getInstance().writeDataToFile(path + "FaultArray." + i, faults);// write all fault rates
        } // for runs         
       
	}

  /**
   * Main method
   * @param args
 * @throws Exception 
   */
  public static void main(String[] args) throws Exception {
    GenerateFromExistingResultsMain gfr = new GenerateFromExistingResultsMain();
    
    String [] fms = {

			// -------------6S------------
			"CounterStrikeSimpleFeatureModel",//24
//			"SPLSSimuelESPnP", //32
//			"DSSample", //41
//			"WebPortal",// * 43    
//			"Drupal", //48
//			"ElectronicDrum",//52
//			"SmartHomev2.2",//60
//			"VideoPlayer", // 71
//			"Amazon", // 79
//			"ModelTransformation", // 88
//			"CocheEcologico",// * 94
//			"Printers",//	172	   								
//						
////			// -------------30S------------
//			"E-shop",//	* 290		    			
//  			"toybox", //544
//			"axTLS", // * 684    			
//			"SPLOT-3CNF-FM-1000-200-0,50-SAT-1",
//			"SPLOT-3CNF-FM-1000-200-0,50-SAT-2",
//			"SPLOT-3CNF-FM-1000-200-0,50-SAT-3",
//			"SPLOT-3CNF-FM-1000-200-0,50-SAT-4",
//			"SPLOT-3CNF-FM-1000-200-0,50-SAT-5",
//			"SPLOT-3CNF-FM-1000-200-0,50-SAT-6",
//			"SPLOT-3CNF-FM-1000-200-0,50-SAT-7",
//			"SPLOT-3CNF-FM-1000-200-0,50-SAT-8",
//			"SPLOT-3CNF-FM-1000-200-0,50-SAT-9",
//			"SPLOT-3CNF-FM-1000-200-0,50-SAT-10",
//					
//			// -------------600S,15 runs------------	
//			"ecos-icse11",// 1244 
//			"freebsd-icse11", // * 1396 
//			"Automotive01", //2513 
//			"SPLOT-3CNF-FM-5000-1000-0,30-SAT-1",// 5000
//			"2.6.28.6-icse11", // * 6888
//			"Automotive02_V3",//18434, YES 			

    		//--------------------------------parameter study---------------------------
//    		"WebPortal",//43    
//    		"CocheEcologico",//94
//    		"E-shop",//	290		    			
//    		"axTLS", //684    			
//			"SPLOT-3CNF-FM-1000-200-0,50-SAT-1",
//			"freebsd-icse11", // 1396 
//			"2.6.28.6-icse11", //6888     		
	};


	int nbPairs = 10000;
	gfr.exisitingT  = 3;
	gfr.t           = 6; // To generate results for t= X, t=0 means faults rate
	gfr.nbProds     = 100;
	gfr.outputDir   = "./output/";
//	gfr.outputDir   = "./outputOrderParameter/";
//	gfr.outputDir   = "./outputParameterR1/";
	gfr.runs        = 1; //runs = 24 for N=50 and 500 
	gfr.algName     = "SAT4JUnpredictable";
//	gfr.algName     = "NS";
//	gfr.algName     = "GA";
//	gfr.algName     = "SamplingDown";
//	gfr.algName     = "Smarch";	
//	gfr.algName     = "NSR1HammingDistance";
//	gfr.algName     = "NSR1DiceDistance";
//	gfr.algName     = "NSR1JaccardDistance";
//	gfr.algName     = "Genetic+TwoSAT";
//	gfr.algName     = "RandomizedSAT4J";
//	gfr.algName     = "NSR1RerunForGenWays";
//	gfr.algName     = "HenardGA";
//	gfr.algName     = "NSR1Nb=N";
	// -----------------Parameter study-----------------------	
//	gfr.algName     = "NSR1P=1.0";		
//	gfr.algName     = "NSR1NbRatio=0.1";		

	// -----------------Parameter study end-----------------------	
	
//	gfr.algName     = "GA";
//	gfr.algName     = "SamplingDown";
//	gfr.algName     = "NSprobSAT";
//	gfr.algName     = "NSSAT4J";
	 
	long timeAllowed = 0; 		

	String fmFile = null;	
	for (int i = 0;i < fms.length;i++) {				
		fmFile = "./all_FM/TSE/" + fms[i] + ".dimacs"; 	
			
		System.out.println(fmFile);
		SPL.getInstance().initializeModelSolvers(fmFile,  gfr.t);
		
		if (SPL.getInstance().numFeatures <= 200) {
			timeAllowed = 6 * 1000; 
		} else if (SPL.getInstance().numFeatures <= 1000){
			timeAllowed = 30 * 1000; 
		} else {
			timeAllowed = 600 * 1000; 
		}
		
//		timeAllowed = timeAllowed / 2;
		 
		gfr.timeAllowed  = timeAllowed;
		
		gfr.computeTwiseCoverage(fmFile);	
//		gfr.computeFaultRate(fmFile);
//		gfr.computeFitness(fmFile);	
 
	} // main
  }
} // 


