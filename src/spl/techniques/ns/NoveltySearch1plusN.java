/* NoveltySearch1plusN.java
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
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 * 
 */
package spl.techniques.ns;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Random;

import jmetal.encodings.variable.Binary;
import jmetal.util.PseudoRandom;
import spl.SPL;
import spl.fm.Product;
import spl.techniques.DistancesUtil;
import spl.techniques.ga.Individual;

/**
 *
 * @author Yi Xiang
 * 
 * This class implements a novelty search with N archived solutions and one population member
*/
public class NoveltySearch1plusN {
	
	List<Product> archive ; // Archive 
    double[][] distancesMatrix; // Distance matrix   
    double [] noveltyScores; 
    
    List<Double> runCoverage ; // record coverage during run
    
	private int archiveSize_; // Archive size
	private int k_; 				// k_ is Nb in the paper
	private double theta_; 			// Threshold of novelty score, default is 0
    private long timeAllowedMS_;   // Running time
    private double p; // Used in the repair operator, a parameter
    
    private static Random random; // 
    boolean matrixInitialized = false; // Matrix  is initialized or not 
    
    public static final int RANDOM_SELECTION = 1;
    public static final int BINARY_SELECTION = 2;
    
    public int minID; 
    public int maxID; 
    
    private long TT50;
    private long TT90;
    private long TT95;
    private boolean TT50Flag = false;
    private boolean TT90Flag = false;
    private boolean TT95Flag = false;
    /**
     * Constructor
     * @param archiveSize
     * @param k
     * @param theta
     * @param timeAllowedMS
     */
    public NoveltySearch1plusN(int archiveSize, int k, double theta, long timeAllowedMS,double p) {
    	this.archiveSize_ = archiveSize;
    	this.k_ = k;
    	this.theta_ = theta;    	
        this.timeAllowedMS_ = timeAllowedMS;
        this.matrixInitialized  = false;
        this.p = p;
        
        this.TT50 = timeAllowedMS;
        this.TT90 = timeAllowedMS;
        this.TT95 = timeAllowedMS;
        
        // 初始化数组
        archive = new ArrayList<Product>(archiveSize_); 
        distancesMatrix = new double [archiveSize_+1][archiveSize_+1]; // plus one because of one population member
        random = new Random();
        noveltyScores = new double [archiveSize_ + 1]; 
        
        runCoverage = new ArrayList<Double> ();

    }
    
    
    /**
     * Update archive using a new product 
     * @param product
     * @return
     */
    public boolean updateAchive(Product product) {
    	
    	if (archive.contains(product)) { // 
    		return false;
    	}
    	
    	if (archive.size() < archiveSize_) {
    		
    		archive.add(product);// 
    		return true;
    		
    	} else { // archive.size() == archiveSize_
    		
    		if (!matrixInitialized) {
    			initializeMatric(product);
    			matrixInitialized = true;
    		}    		            
            
    		distancesMatrix[archiveSize_][archiveSize_] = 0.0;
            for (int i = 0; i < archive.size(); i++) {
//            	distancesMatrix[archiveSize_][i] = DistancesUtil.getJaccardDistance(product,archive.get(i));
//            	distancesMatrix[archiveSize_][i] = DistancesUtil.getHammingDistance(product,archive.get(i));
//            	distancesMatrix[archiveSize_][i] = DistancesUtil.getDiceDistance(product,archive.get(i));
            	distancesMatrix[archiveSize_][i] = DistancesUtil.getAntiDiceDistance(product,archive.get(i));
            	distancesMatrix[i][archiveSize_] = distancesMatrix[archiveSize_][i];
            }
    		
    	}
    	
    	// Obtain the novelty scores    	
    	// reset novelty scores
    	for (int i = 0; i < noveltyScores.length;i++) {
    		noveltyScores[i] = 0.0;
    	}
    	
    	double [] dist = new double [archiveSize_ + 1]; 
    	int []    idx =  new int [archiveSize_ + 1]; 
    			
    	for (int i = 0; i <= archiveSize_;i++) {
    		
    		for (int j = 0; j <= archiveSize_; j++) {
    			dist[j] = distancesMatrix[i][j];
    			idx[j] = j;
    		}
    		
    		/* Find the k-nearest neighbors*/
    		DistancesUtil.minFastSort(dist, idx, archiveSize_ + 1, k_);
    		
    		noveltyScores[i] = 0.0;    		
    		for (int k = 0; k < k_; k++) {
    			noveltyScores[i] = noveltyScores[i] + dist[k];
    		}
    		
    		noveltyScores[i] = noveltyScores[i]/k_; // the average value
    		
    	} // for i
    	   	
    	
    	//Find the solution with worst (smallest) novelty score
    	double minScore = Double.MAX_VALUE;
    	minID  = -1;
    	
    	double maxScore = - Double.MAX_VALUE;
    	maxID  = -1;
    	
        for (int i = 0; i < archiveSize_; i++) {          
                if (noveltyScores[i] < minScore) {
                	minScore = noveltyScores[i];
                	minID = i;
                }
                
                if (noveltyScores[i] > maxScore) {
                	maxScore = noveltyScores[i];
                	maxID = i;
                } 
        }
          
                
        // Try to replace the worst member        
		if (noveltyScores[archiveSize_]  > theta_ && (noveltyScores[archiveSize_] > minScore)) {
			archive.set(minID, product); // replace
			
//			System.out.println("noveltyScores[archiveSize_]" + noveltyScores[archiveSize_] +",minScore"  + minScore);
			// Update the distance matrix
			for (int j=0;j < archiveSize_; j++) {
				distancesMatrix[minID][j] = distancesMatrix[archiveSize_][j];
				distancesMatrix[j][minID] = distancesMatrix[j][archiveSize_];
			}
			
			distancesMatrix[minID][minID] = 0.0;
			noveltyScores[minID] = noveltyScores[archiveSize_];
			return true;
		}    		
		
    	return false;
    }
    
    /**
     * Update archive using a new product 
     * @param product
     * @return
     */
    public boolean updateAchiveEfficient(Product product) {
    	
    	if (archive.contains(product)) { // 已存在相同的个体，直接返回
    		return false;
    	}
    	
    	if (archive.size() < archiveSize_) {
    		
    		archive.add(product);// 直接将product加入    	
    		return true;
    		
    	} else { // archive.size() == archiveSize_
    		
    		if (!matrixInitialized) {
    			initializeMatric(product);
    			matrixInitialized = true;
    		}    		
            
            // 计算个体product与每个archive member 的距离
    		distancesMatrix[archiveSize_][archiveSize_] = 0.0;
            for (int i = 0; i < archive.size(); i++) {
            	distancesMatrix[archiveSize_][i] = DistancesUtil.getJaccardDistance(product,archive.get(i));
            	distancesMatrix[i][archiveSize_]= distancesMatrix[archiveSize_][i];
            }
    		
    	}
    	
    	// Obtain the novelty scores
    	
    	// reset novelty scores
    	for (int i = 0; i < noveltyScores.length;i++) {
    		noveltyScores[i] = 0.0;
    	}
    	
    	double [] dist = new double [archiveSize_ + 1]; 
    	int []    idx =  new int [archiveSize_ + 1]; 
    			
    	for (int i = 0; i <= archiveSize_;i++) {
    		
    		for (int j = 0; j <= archiveSize_; j++) {
    			dist[j] = distancesMatrix[i][j];
    			idx[j] = j;
    		}
    		
    		/* Find the k-nearest neighbors*/
    		DistancesUtil.minFastSort(dist, idx, archiveSize_ + 1, k_);
    		
    		noveltyScores[i] = 0.0;    		
    		for (int k = 0; k < k_; k++) {
    			noveltyScores[i] = noveltyScores[i] + dist[k];
    		}
    		
    		noveltyScores[i] = noveltyScores[i]/k_; // the average value
    		
    	} // for i
    	   	
    	
    	//Find the solution with worst (smallest) novelty score
    	double minScore = Double.MAX_VALUE;
    	minID  = -1;
    	
    	double maxScore = - Double.MAX_VALUE;
    	maxID  = -1;
    	
        for (int i = 0; i < archiveSize_; i++) {          
                if (noveltyScores[i] < minScore) {
                	minScore = noveltyScores[i];
                	minID = i;
                }
                
                if (noveltyScores[i] > maxScore) {
                	maxScore = noveltyScores[i];
                	maxID = i;
                } 
        }
          
                
        // Try to replace the worst member        
		if (noveltyScores[archiveSize_]  > theta_ && (noveltyScores[archiveSize_] > minScore)) {
			archive.set(minID, product); // replace
			
//			System.out.println("noveltyScores[archiveSize_]" + noveltyScores[archiveSize_] +",minScore"  + minScore);
			// Update the distance matrix
			for (int j=0;j < archiveSize_; j++) {
				distancesMatrix[minID][j] = distancesMatrix[archiveSize_][j];
				distancesMatrix[j][minID] = distancesMatrix[j][archiveSize_];
			}
			
			distancesMatrix[minID][minID] = 0.0;
			noveltyScores[minID] = noveltyScores[archiveSize_];
			return true;
		}    		
		
    	return false;
    }
    
    public List<Product> getArchive() {
		return archive;
	}

	public void setArchive(List<Product> archive) {
		this.archive = archive;
	}

	/**
     * 初始化距离矩阵
     * @param product
     */
    public void initializeMatric(Product product) {
    	// Computation of the distances
        for (int i = 0; i < archiveSize_; i++) {
        	distancesMatrix[i][i] = 0.0;
        	
            for (int j = i + 1; j < archiveSize_; j++) {   
//                double dist = DistancesUtil.getJaccardDistance(archive.get(i), archive.get(j)); 
//            	 double dist = DistancesUtil.getHammingDistance(archive.get(i), archive.get(j));            	 
//            	double dist = DistancesUtil.getDiceDistance(archive.get(i), archive.get(j)); 
            	double dist = DistancesUtil.getAntiDiceDistance(archive.get(i), archive.get(j));             	
                distancesMatrix[i][j] = dist;       
                distancesMatrix[j][i] = dist;  
            } // for j
        } // for i
        
    } // initializeMatric
    
    
    
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
    
    /**
     * 将Binary转换成product
     * @param vector
     * @return
     */
    public Product bin2Product(Binary bin) {

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
    
   public Product mutate(Product prod, double probability) {
	  
	   Binary bin = Product2Bin(prod);	   
	   	
    	for (Integer j : SPL.getInstance().featureIndicesAllowedFlip){ //flip only not "fixed" features
			
       	 if (PseudoRandom.randDouble() < probability) {								
       		 	bin.bits_.flip(j);							
			}
		}
    	
    	return bin2Product(bin);
    	
    }
    
   /**
    *  
    * @param prod1
    * @param prod2
    * @param probability
    * @return
    */
   public Product [] crossover(Product prod1, Product prod2, double probability) {
		  
	   Binary parent1 = Product2Bin(prod1);	   
	   Binary parent2 = Product2Bin(prod2);	
	   Binary [] offSpringBin = new Binary[2];
	   
	   offSpringBin[0] = new Binary(prod1.size());
	   offSpringBin[1] = new Binary(prod2.size());
			   
	   Product [] offSpring = new  Product [2];
	   
	   if (PseudoRandom.randDouble() < probability) {
	    	for (int i = 0;i < parent1.getNumberOfBits();i++){ 
	    		
	    		if (PseudoRandom.randDouble() < 0.5) {
	        		boolean value = parent1.getIth(i);	        
	        		offSpringBin[0].setIth(i, value);	        		
	        		
	        		value = parent2.getIth(i);
	        		offSpringBin[1].setIth(i, value);
	        	
	  			} else {
	  				boolean value = parent2.getIth(i);
	  				offSpringBin[0].setIth(i, value);
	        		
	        		value = parent1.getIth(i);	        
	        		offSpringBin[1].setIth(i, value);
	
	  			} // if
	       	
			} // for i
	    	
	    	offSpring[0] = bin2Product(offSpringBin[0]);
	    	offSpring[1] = bin2Product(offSpringBin[1]);
	    	 
	   } else{// if  (PseudoRandom.randDouble() < probability) {
		   
		   offSpring[0] = prod1;
		   offSpring[1] = prod2;
	   }
    	    	
	   return offSpring;  
    	 	
    }
   
   /**
    * Select two parents based on novelty scores
    * @return
    */
   public Product [] selection(int strategy) {
	   Product [] parents = new Product [2];
	   int p1 = -1,p2 = 0;
	   
	   if (strategy == RANDOM_SELECTION) {
		   p1 = PseudoRandom.randInt(0, archive.size() - 1);
		   p2 = PseudoRandom.randInt(0, archive.size() - 1);
		   while (p2==p1) {
			   p2 = PseudoRandom.randInt(0, archive.size() - 1); 
		   }
	   } else if (strategy == BINARY_SELECTION) {
		   
		  p1 = binarySelection();
		  p2 = binarySelection();
		  
		  while (p2==p1) {
			   p2 = binarySelection(); 
		   }
		  		   
	   }
	   
	   parents[0] = archive.get(p1);
	   parents[1] = archive.get(p2);
	   
	   return parents;	   
   }
   
   
   public int binarySelection() {
	   int r1 = PseudoRandom.randInt(0, archive.size() - 1);
	   int r2 = PseudoRandom.randInt(0, archive.size() - 1);
	   while (r2==r1) {
		   r2 = PseudoRandom.randInt(0, archive.size() - 1); 
	   }
	   
	   if (noveltyScores[r1] > noveltyScores[r2]) {
		   return r1;
	   } else if (noveltyScores[r2] > noveltyScores[r1]) {
		   return r2;
	   } else {
		   if (PseudoRandom.randDouble() < 0.5) 
			   return r1;
		   else
			   return r2;
	   }
	   
   }
   
// for testing
   public int binarySelection(int r1, int r2) {
	 	while (r2==r1) {
	 		r2 = PseudoRandom.randInt(0, archive.size() - 1); 
	 	}
	 	
	 	if (noveltyScores[r1] > noveltyScores[r2]) {
	 		return r1;
	 	} else if (noveltyScores[r2] > noveltyScores[r1]) {
	 		return r2;
	 	} else {
	 		if (PseudoRandom.randDouble() < 0.5) 
	 			return r1;
	 		else
	 			return r2;
	 	}
   }
	
   
	public void setNoveltyScores(double[] noveltyScores) {
		this.noveltyScores = noveltyScores;
	}
	
    public List<Product> runNS(double  probability, int mutateType) throws Exception {
        long startTimeMS = System.currentTimeMillis();
        
        //初始化一组解
        archive = SPL.getInstance().getUnpredictableProducts(archiveSize_);
       
//        double [] fitnessNS = new double [archiveSize_];
//        fitnessNS = SPL.getInstance().computeFitnessSums(archive, SimilarityTechnique.JACCARD_DISTANCE);
//        double[] fitnessValuesNS = new double[archiveSize_];
//        
//        for (int j = 0; j < fitnessValuesNS.length; j++) {
//            fitnessValuesNS[j] += fitnessNS[j];
//        }
//        System.out.println("初始的累积适应值=" + fitnessValuesNS[archiveSize_ - 1]);
        
        
        while (System.currentTimeMillis() - startTimeMS < timeAllowedMS_) {
        	Product product = null;
     
//        	Product [] parents = selection(RANDOM_SELECTION);
        	
        	Product [] parents = selection(BINARY_SELECTION);
        	Product [] offspring = crossover(parents[0], parents[1],1);
        	offspring[0] = mutate(offspring[0],0.5);
          	offspring[1] = mutate(offspring[1],0.5);
//    		 int randomID = minID; //random.nextInt(archiveSize_);        		
//        		 product = SPL.getInstance().getUnpredictableProductsSMT(archive.get(randomID));   
//    		 product = SPL.getInstance().getRandomProducts();   
     
          	offspring[0] = SPL.getInstance().repairProducts(offspring[0],0.1);
          	offspring[1] = SPL.getInstance().repairProducts(offspring[1],0.1);
          	
        	updateAchive(offspring[0]);
        	updateAchive(offspring[1]);
        	
        	//Print fitness
//        	 fitnessNS = SPL.getInstance().computeFitnessSums(archive, SimilarityTechnique.JACCARD_DISTANCE);
//             fitnessValuesNS = new double[archiveSize_];
             
//             for (int j = 0; j < fitnessValuesNS.length; j++) {
//                 fitnessValuesNS[j] += fitnessNS[j];
//             }
//             System.out.println("迭代过程累积适应值=" + fitnessValuesNS[archiveSize_ - 1]);
        }
        
        return archive;                
       
    }
    
    
    public int runNS_Convergence(String path,  int numberOfPoints, int individualSize, int type) throws Exception {
    	long sumTimeMS = 0;       
                                    
//        archive = SPL.getInstance().getUnpredictableProducts(archiveSize_);
    	archive = SPL.getInstance().loadProductsFromFile(path.replaceAll("NSprobSAT", "GA") + "Products.0");
    	
    	
        int nbIter = 0;       		
        long startTimeMS = System.currentTimeMillis();
        int interval = (int) ((timeAllowedMS_ - sumTimeMS)/(numberOfPoints - 1));
        
      // Record time	
        int recordTimes = 0;  
    	timeRecord(path,archive,recordTimes); 
        recordTimes++;   
                        
        while (sumTimeMS < timeAllowedMS_) {
        	
        	startTimeMS = System.currentTimeMillis();
        	
        	Product product = null;     
//        	Product [] parents = selection(RANDOM_SELECTION);        	
        	Product [] parents = selection(BINARY_SELECTION);
        	Product [] offspring = crossover(parents[0], parents[1],1);
        	
        	offspring[0] = mutate(offspring[0],0.5);
          	offspring[1] = mutate(offspring[1],0.5);  
          	
          	offspring[0] = SPL.getInstance().repairProducts(offspring[0],p);
          	offspring[1] = SPL.getInstance().repairProducts(offspring[1],p);  
          	        
          	
          	if (sumTimeMS >  0.5 * timeAllowedMS_)
          	      theta_ = 0.0;
          	
          	updateAchive(offspring[0]);
        	updateAchive(offspring[1]);

        	nbIter++;
            
        	// -------------------Record time------------------
        	sumTimeMS = sumTimeMS + (System.currentTimeMillis() - startTimeMS); //  累加时间  
        	if (sumTimeMS >= (recordTimes - 1) * interval && sumTimeMS >= (recordTimes) * interval) {
             	timeRecord(path,archive,recordTimes); 
             	recordTimes++;          
            }            
        }
        
        noveltyBasedSort();
        System.out.println("-----------nbIter in NS------------- " + nbIter);
        System.out.println("-----------sumTimeMS in NS------------- " + sumTimeMS); 
        return recordTimes;                
       
    }
    
    /**
     * Record time stones
     * @param indiv
     * @throws Exception 
     */
    public void timeRecord(String path, List<Product> archive,int recordTimes) throws Exception {
    	
    	(SPL.getInstance()).writeProductsToFile(path + "Products." + recordTimes, archive);      
       
    }
    
    public List<Product> runNS(int individualSize, int type) throws Exception {
    	long sumTimeMS = 0;
    	 
        long startTimeMS = System.currentTimeMillis();
        
        //初始化一组解
        archive = SPL.getInstance().getUnpredictableProducts(archiveSize_);
             
//        archive =SPL.getInstance().getRandomProductsAssume(archiveSize_,
//        								SPL.getInstance().featuresMap, 
//        								SPL.getInstance().featuresList,0.1); //生成一组随机解      
        int nbIter = 0;
        
//        System.out.println("score = " + this.theta_);
        
        // -------------------Record time------------------
        sumTimeMS = System.currentTimeMillis() - startTimeMS;		       
//        timeRecord(archive,sumTimeMS); 
                        
        while (sumTimeMS < timeAllowedMS_) {
        	
        	startTimeMS = System.currentTimeMillis();
        	
        	Product product = null;     
        	//Product [] parents = selection(RANDOM_SELECTION);        	
        	Product [] parents = selection(BINARY_SELECTION);
        	Product [] offspring = crossover(parents[0], parents[1],1);        	
        	offspring[0] = mutate(offspring[0],0.5);
          	offspring[1] = mutate(offspring[1],0.5);            	
          	offspring[0] = SPL.getInstance().repairProducts(offspring[0],p);
          	offspring[1] = SPL.getInstance().repairProducts(offspring[1],p);            	        
          	//--------------------------------------------------------------
        	
          	
          	// Random way
//        	Product [] offspring = new Product [2];
//        	offspring[0] = SPL.getInstance().getRandomProducts();
//        	offspring[1] = SPL.getInstance().getRandomProducts();
        	//-------------------Random way----------------------------
          	
          	updateAchive(offspring[0]);
        	updateAchive(offspring[1]);

        	nbIter++;
            
        	// -------------------Record time------------------
        	sumTimeMS = sumTimeMS + (System.currentTimeMillis() - startTimeMS); //  累加时间   
//            timeRecord(archive,sumTimeMS);     
        }
        
        noveltyBasedSort();
        System.out.println("-----------nbIter in NS------------- " + nbIter);
        System.out.println("-----------sumTimeMS in NS------------- " + sumTimeMS); 
        return archive;                
       
    }
    
    /** Version R1
       * Run NS algorithm  
     * @return
     * @throws Exception
     */
    public List<Product> runNSR1(String outputDir, String fmFileName,int currentRun,int [] evaluations) throws Exception {
    	long sumTimeMS = 0;
    	 
        long startTimeMS = System.currentTimeMillis();
        
        //Randomly generate a set of products
//        archive = SPL.getInstance().getUnpredictableProducts(archiveSize_);
        
        // Load products from SAT4JUnpredictableR1 for fair comparison
        String loadPath = "./output/SAT4JUnpredictable/" + fmFileName + "/Samples/" + archiveSize_ + "prods/"+ (timeAllowedMS_ / 1) + "ms/"; // 
        archive = SPL.getInstance().loadProductsFromFile(loadPath + "Products." + currentRun);
                        
        
        int nbIter = archiveSize_;
        
//        System.out.println("score = " + this.theta_);
        
        // -------------------Record time------------------
        sumTimeMS = System.currentTimeMillis() - startTimeMS;		       
//        timeRecord(archive,sumTimeMS);   
    	
        while (sumTimeMS < timeAllowedMS_) {
        	
        	startTimeMS = System.currentTimeMillis();
        	
        	//-------------------------------Method 1: crossover + mutation------------------------------------
//        	Product product = null; 
//        	Product [] parents = selection(BINARY_SELECTION);
//        	Product [] offspring = crossover(parents[0], parents[1],1);        	
//        	offspring[0] = mutate(offspring[0],0.5);
//            offspring[1] = mutate(offspring[1],0.5);            	
//            offspring[0] = SPL.getInstance().repairProducts(offspring[0],p);
//            offspring[1] = SPL.getInstance().repairProducts(offspring[1],p);            	        
          	//--------------------------------crossover + mutation(end)-------------------------------
        	
          	
          	//---------------------------- Method 2: Random way-----------------------------------
        	Product [] offspring = new Product [2];
        	offspring[0] = SPL.getInstance().getRandomProducts(p);
        	offspring[1] = SPL.getInstance().getRandomProducts(p);
        	//--------------------------------Random way (end)-------------------------------------
          	
        	// Update archive
          	updateAchive(offspring[0]);
        	updateAchive(offspring[1]);

        	nbIter = nbIter + 2;
            
        	// -------------------Record time------------------
        	sumTimeMS = sumTimeMS + (System.currentTimeMillis() - startTimeMS); //  累加时间   
//            timeRecord(archive,sumTimeMS);     
        }
        
        evaluations[currentRun] = nbIter;
        
        System.out.println("-----------nbIter in NS------------- " + nbIter);
        System.out.println("-----------sumTimeMS in NS------------- " + sumTimeMS); 
        return archive;                
       
    }
    
    
    
    public void noveltyBasedSort() {
    	 List <Product> productCopy = new ArrayList <Product>(archive);
    	     	 
    	 int [] idx = new int[noveltyScores.length - 1];
    	 for (int i = 0; i < idx.length;i++) {
    		 idx[i] = i;
    	 }
    	 
    	 DistancesUtil.maxFastSort(noveltyScores, idx, archiveSize_ , archiveSize_);
    	 
    	 for (int i = 0; i < idx.length;i++) {
    		 archive.set(i, productCopy.get(idx[i]));
    	 }
    	 
    }
    
    /**
     * Record time stones
     * @param indiv
     * @throws Exception 
     */
    public void timeRecord(String path, Individual indiv,int recordTimes) throws Exception {
    	
    	(SPL.getInstance()).writeProductsToFile(path + "Products." + recordTimes, indiv.getProducts());      
       
    }
    
    /**
     * Record time stones
     * @param indiv
     */
    public void timeRecord(List <Product> products,long sumTimeMS) {
    	
        double cov = SPL.getInstance().getCoverage(products);
        
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
    /**
     * 初始和过程均采用随机SAT4J生成新个体
     * @param individualSize
     * @param type
     * @return
     * @throws Exception
     */
    public List<Product> runSimpleNS() throws Exception {
        long startTimeMS = System.currentTimeMillis();
        
        //初始化一组解
        archive = SPL.getInstance().getUnpredictableProducts(archiveSize_);

        while (System.currentTimeMillis() - startTimeMS < timeAllowedMS_) {
        	
        	Product product = null;          	
    		product = SPL.getInstance().getUnpredictableProduct();    		
        	updateAchive(product);     

        }
        
        return archive;                
       
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

} // Class
