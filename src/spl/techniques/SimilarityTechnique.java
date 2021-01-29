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
import java.util.List;

import spl.fm.Product;

/**
 *
 * @author Christopher Henard
 */
public class SimilarityTechnique implements PrioritizationTechnique {

    public static final int JACCARD_DISTANCE = 1;
    public static final int GREEDY_SEARCH = 2;
    public static final int NEAR_OPTIMAL_SEARCH = 3;
    public static final int Anti_Dice_Distance = 4;
    private int distanceMethod;
    private int searchMethod;
    private double lastFitnessComputed;

    public SimilarityTechnique(int distanceMethod, int searchMethod) {
        this.distanceMethod = distanceMethod;
        this.searchMethod = searchMethod;
        lastFitnessComputed = -1;
    }

    // should be called after one prioritization
    public double getLastFitnessComputed() {
        return lastFitnessComputed;
    }

    public void setLastFitnessComputed(double lastFitnessComputed) {
        this.lastFitnessComputed = lastFitnessComputed;
    }

    
    public double PD( List<Product> products) {
      int n = products.size(); // n products
  	 
  	 
  	  double [][] D = new double [n][n];
  	  int [] min_index = new int [n];
  	  double [] min_d = new double [n];
  	  boolean [] removed = new boolean [n];
  	  
  	  double PD = 0.0;
  	  
  	  // Step 1: Construct D matrix 
  	  for (int i = 0; i < n; i++) {
  		  for (int j = 0; j < n; j++) {
  			  if (i == j) {
  				  D[i][j] = Double.MAX_VALUE;			
  			  } else if (j>i) {
  				  D[i][j] = DistancesUtil.getJaccardDistance(products.get(i),products.get(j));	
//  				  D[i][j] = DistancesUtil.getDiceDistance(products.get(i),products.get(j));	
//  				 D[i][j] = DistancesUtil.getAntiDiceDistance(products.get(i),products.get(j));	
//  				D[i][j] = DistancesUtil.getSetBasedDifference(products.get(i),products.get(j));	
  				  D[j][i] = D[i][j];
  			  }
  		  }
  	  }
  	  
  	  for (int r = 0; r < n - 1 ; r ++) {
  	  
  		  for (int i = 0; i < n ; i++) {
  			  if (removed[i] == true) {
  				  continue;
  			  }
  			  
  			  min_index[i] = -1;
  			  min_d [i] = Double.MAX_VALUE;
  			  
  			  for (int j = 0; j < n;j ++ ) {
  				  if (D[i][j] < min_d [i]) {
  					  min_d [i] = D[i][j];
  					  min_index[i] = j; 
  				  }
  			  }
  			
  		  } // for i
  	  
  		  double max_min_d = Double.MIN_VALUE;
  		  int    max_min_d_Idx = - 1;
  		  
  		  for (int k = 0; k < n;k++) {
  			  
  			  if (removed[k] == true) {
  				  continue;
  			  }
  			  
  			  if (min_d [k] > max_min_d) {
  				  max_min_d = min_d [k];
  				  max_min_d_Idx = k;
  			  }
  			  
  		  } // for k
  		  
  		  if (max_min_d_Idx!= -1) {
  			  
  			  PD = PD + max_min_d;
  			  
  			  removed[max_min_d_Idx] = true;
  			  
  			  D[min_index[max_min_d_Idx]][max_min_d_Idx] =  Double.MAX_VALUE;
  		  }
  		 
  		  	  
  	  } // for r 	  

        return PD;

    } // PD
    
   
    public double[][] calculateDistanceMatrix(List<Product> products) {
    	int n = products.size();
    	double [][] distancesMatrix = new double [n][n];    	   	
    	
    	 for (int i = 0; i < n; i++) {
         	distancesMatrix[i][i] = 0.0;
         	
             for (int j = i + 1; j < n; j++) {   
                 double dist = DistancesUtil.getJaccardDistance(products.get(i), products.get(j));
                 distancesMatrix[i][j] = dist;       
                 distancesMatrix[j][i] = dist;  
             } // for j
         } // for i
    	    	     
    	 return distancesMatrix;
    	
    }
    
	/**
	 * Return the sum of novelty scores
	 * @param product
	 * @return
	 */
    public double noveltyScoreSum(List<Product> products, int k_) {
    	
    	int n = products.size();
    	
    	double [][] distancesMatrix = new double [n][n];
    	double [] noveltyScores =  new double [n];
    	
    	 for (int i = 0; i < n; i++) {
         	distancesMatrix[i][i] = 0.0;
         	
             for (int j = i + 1; j < n; j++) {   
                 double dist = DistancesUtil.getAntiDiceDistance(products.get(i), products.get(j));
                 distancesMatrix[i][j] = dist;       
                 distancesMatrix[j][i] = dist;  
             } // for j
         } // for i
    	    	     
    	
    	// Obtain the novelty scores    	
    	// reset novelty scores
    	for (int i = 0; i < noveltyScores.length;i++) {
    		noveltyScores[i] = 0.0;
    	}
    	
    	double noveltyScoresSum = 0.0;
    	
    	double [] dist = new double [n]; 
    	int []    idx =  new int [n]; 
    			
    	for (int i = 0; i < n;i++) {
    		
    		for (int j = 0; j < n; j++) {
    			dist[j] = distancesMatrix[i][j];
    			idx[j] = j;
    		}
    		
    		/* Find the k-nearest neighbors*/
    		DistancesUtil.minFastSort(dist, idx, n, k_);
    		
    		noveltyScores[i] = 0.0;    		
    		for (int k = 0; k < k_; k++) {
    			noveltyScores[i] = noveltyScores[i] + dist[k];
//    			System.out.println("k = " + k + ", dist[k] = " + dist[k]);
    		}
//    		System.out.println("----------------------");
    		
    		noveltyScores[i] = noveltyScores[i]/k_; // the average value
    		
    		noveltyScoresSum = noveltyScoresSum + noveltyScores[i];
    	} // for i
    	   	
    	return noveltyScoresSum;
    }
    
    /**
	 * Return the sum of novelty scores
	 * @param product
	 * @return
	 */
    public double noveltyScoreSum(double [][] distancesMatrix, int k_) {
    	
    	int n = distancesMatrix.length;    	
    	
    	double [] noveltyScores =  new double [n]; 	
    	
    	// Obtain the novelty scores    	
    	// reset novelty scores
    	for (int i = 0; i < noveltyScores.length;i++) {
    		noveltyScores[i] = 0.0;
    	}
    	
    	double noveltyScoresSum = 0.0;
    	
    	double [] dist = new double [n]; 
    	int []    idx =  new int [n]; 
    			
    	for (int i = 0; i < n;i++) {
    		
    		for (int j = 0; j < n; j++) {
    			dist[j] = distancesMatrix[i][j];
    			idx[j] = j;
    		}
    		
    		/* Find the k-nearest neighbors*/
    		DistancesUtil.minFastSort(dist, idx, n, k_);
    		
    		noveltyScores[i] = 0.0;    		
    		for (int k = 0; k < k_; k++) {
    			noveltyScores[i] = noveltyScores[i] + dist[k];
//    			System.out.println("k = " + k + ", dist[k] = " + dist[k]);
    		}
//    		System.out.println("----------------------");
    		
    		noveltyScores[i] = noveltyScores[i]/k_; // the average value
    		
    		noveltyScoresSum = noveltyScoresSum + noveltyScores[i];
    	} // for i
    	   	
    	return noveltyScoresSum;
    }
    
    @Override
    public List<Product> prioritize(List<Product> products) {
        int size = products.size();
        List<Product> prioritizedProducts = new ArrayList<Product>(size);
        List<Product> productsCopy = new ArrayList<Product>(products);
        double[][] distancesMatrix = new double[size][size];

        lastFitnessComputed = 0;
        // Computation of the distances
        for (int i = 0; i < distancesMatrix.length; i++) {
            for (int j = 0; j < distancesMatrix.length; j++) {
                distancesMatrix[i][j] = -1;
                if (j > i) {
                    switch (distanceMethod) {
                        case JACCARD_DISTANCE:
                            double dist = DistancesUtil.getJaccardDistance(productsCopy.get(i), productsCopy.get(j));
                            lastFitnessComputed += dist;
                            distancesMatrix[i][j] = dist;
                            break;
                            
                        case Anti_Dice_Distance:
                            double distaADD = DistancesUtil.getAntiDiceDistance(productsCopy.get(i), productsCopy.get(j));
                            lastFitnessComputed += distaADD;
                            distancesMatrix[i][j] = distaADD;
                            break;                                
                            
                        default:
                            ;
                    }

                }

            }
        }

        // Selection
        switch (searchMethod) {
            case GREEDY_SEARCH:
                while (!productsCopy.isEmpty()) {
                    if (productsCopy.size() != 1) {
                        double dmax = -1;
                        int toAddIIndex = -1;
                        int toAddJIndex = -1;
                        for (int i = 0; i < distancesMatrix.length; i++) {
                            for (int j = 0; j < distancesMatrix.length; j++) {
                                if (j > i) {
                                    if (distancesMatrix[i][j] > dmax) {
                                        dmax = distancesMatrix[i][j];
                                        toAddIIndex = i;
                                        toAddJIndex = j;
                                    }
                                }
                            }
                        }

                        Product pi = products.get(toAddIIndex);
                        Product pj = products.get(toAddJIndex);
                        prioritizedProducts.add(pi);
                        prioritizedProducts.add(pj);
                        productsCopy.remove(pi);
                        productsCopy.remove(pj);

                        for (int i = 0; i < distancesMatrix.length; i++) {
                            distancesMatrix[toAddIIndex][i] = distancesMatrix[i][toAddIIndex] = distancesMatrix[i][toAddJIndex] = distancesMatrix[toAddJIndex][i] = -1;
                        }
                    } else {
                        prioritizedProducts.add(productsCopy.get(0));
                        productsCopy.clear();
                    }
                }
                break;

            case NEAR_OPTIMAL_SEARCH:
                List<Integer> possibleIndices = new ArrayList<Integer>();
                List<Integer> doneIndices = new ArrayList<Integer>();
                for (int i = 0; i < size; i++) {
                    possibleIndices.add(i);

                }
                double maxDistance = -1;
                int toAddIIndex = -1;
                int toAddJIndex = -1;
                for (int i = 0; i < distancesMatrix.length; i++) {
                    for (int j = 0; j < distancesMatrix.length; j++) {
                        if (j > i) {
                            if (distancesMatrix[i][j] > maxDistance) {
                                maxDistance = distancesMatrix[i][j];
                                toAddIIndex = i;
                                toAddJIndex = j;
                            }
                        }
                    }
                }
                Product pi = products.get(toAddIIndex);
                Product pj = products.get(toAddJIndex);

                prioritizedProducts.add(pi);
                prioritizedProducts.add(pj);
                productsCopy.remove(pi);
                productsCopy.remove(pj);
                possibleIndices.remove((Integer) toAddIIndex);
                possibleIndices.remove((Integer) toAddJIndex);
                doneIndices.add(toAddIIndex);
                doneIndices.add(toAddJIndex);


                while (!productsCopy.isEmpty()) {
                    
                    
                    
                    if (possibleIndices.size() > 1) {
                        double maxDist = -1;
                        int toAdd = -1;
                        for (Integer i : possibleIndices) {

                            double distance = 0;
                            for (Integer j : doneIndices) {
                                distance += (j > i) ? distancesMatrix[i][j] : distancesMatrix[j][i];
                            }
                            if (distance > maxDist) {
                                maxDist = distance;
                                toAdd = i;
                            }
                        }
                        Product p = products.get(toAdd);

                        prioritizedProducts.add(p);
                        productsCopy.remove(p);
                        possibleIndices.remove((Integer) toAdd);
                        doneIndices.add(toAdd);

                    } else {
                        prioritizedProducts.add(products.get(possibleIndices.get(0)));
                        productsCopy.clear();
                    }
                }
            default:
                break;
        }
        return prioritizedProducts;
    }
    
    public List<Product> prioritize2(List<Product> products) {
        int size = products.size();
        List<Product> prioritizedProducts = new ArrayList<Product>(size);
        List<Product> productsCopy = new ArrayList<Product>(products);
        double[][] distancesMatrix = new double[size][size];

        lastFitnessComputed = 0;
        // Computation of the distances
        for (int i = 0; i < distancesMatrix.length; i++) {
            for (int j = 0; j < distancesMatrix.length; j++) {
                distancesMatrix[i][j] = -1;
                if (j > i) {
                    switch (distanceMethod) {
                        case JACCARD_DISTANCE:
                            double dist = DistancesUtil.getJaccardDistance(productsCopy.get(i), productsCopy.get(j));
                            lastFitnessComputed += dist;
                            distancesMatrix[i][j] = dist;
                            break;
                        default:
                            ;
                    }

                }

            }
        }

        // Selection
        switch (searchMethod) {
            case GREEDY_SEARCH:
                while (!productsCopy.isEmpty()) {
                    if (productsCopy.size() != 1) {
                        double dmax = -1;
                        int toAddIIndex = -1;
                        int toAddJIndex = -1;
                        for (int i = 0; i < distancesMatrix.length; i++) {
                            for (int j = 0; j < distancesMatrix.length; j++) {
                                if (j > i) {
                                    if (distancesMatrix[i][j] > dmax) {
                                        dmax = distancesMatrix[i][j];
                                        toAddIIndex = i;
                                        toAddJIndex = j;
                                    }
                                }
                            }
                        }

                        Product pi = products.get(toAddIIndex);
                        Product pj = products.get(toAddJIndex);
                        prioritizedProducts.add(pi);
                        prioritizedProducts.add(pj);
                        productsCopy.remove(pi);
                        productsCopy.remove(pj);

                        for (int i = 0; i < distancesMatrix.length; i++) {
                            distancesMatrix[toAddIIndex][i] = distancesMatrix[i][toAddIIndex] = distancesMatrix[i][toAddJIndex] = distancesMatrix[toAddJIndex][i] = -1;
                        }
                    } else {
                        prioritizedProducts.add(productsCopy.get(0));
                        productsCopy.clear();
                    }
                }
                break;

            case NEAR_OPTIMAL_SEARCH:
                List<Integer> possibleIndices = new ArrayList<Integer>();
                List<Integer> doneIndices = new ArrayList<Integer>();
                for (int i = 0; i < size; i++) {
                    possibleIndices.add(i);

                }
                double maxDistance = -1;
                int toAddIIndex = -1;
                int toAddJIndex = -1;
                for (int i = 0; i < distancesMatrix.length; i++) {
                    for (int j = 0; j < distancesMatrix.length; j++) {
                        if (j > i) {
                            if (distancesMatrix[i][j] > maxDistance) {
                                maxDistance = distancesMatrix[i][j];
                                toAddIIndex = i;
                                toAddJIndex = j;
                            }
                        }
                    }
                }
                Product pi = products.get(toAddIIndex);
                Product pj = products.get(toAddJIndex);

                prioritizedProducts.add(pi);
                prioritizedProducts.add(pj);
                productsCopy.remove(pi);
                productsCopy.remove(pj);
                possibleIndices.remove((Integer) toAddIIndex);
                possibleIndices.remove((Integer) toAddJIndex);
                doneIndices.add(toAddIIndex);
                doneIndices.add(toAddJIndex);


                while (!productsCopy.isEmpty()) {
                    if (prioritizedProducts.size() >= 2000){
                        return prioritizedProducts;
                    }
                    
                    
                    if (possibleIndices.size() > 1) {
                        double maxDist = -1;
                        int toAdd = -1;
                        for (Integer i : possibleIndices) {

                            double distance = 0;
                            for (Integer j : doneIndices) {
                                distance += (j > i) ? distancesMatrix[i][j] : distancesMatrix[j][i];
                            }
                            if (distance > maxDist) {
                                maxDist = distance;
                                toAdd = i;
                            }
                        }
                        Product p = products.get(toAdd);

                        prioritizedProducts.add(p);
                        productsCopy.remove(p);
                        possibleIndices.remove((Integer) toAdd);
                        doneIndices.add(toAdd);

                    } else {
                        prioritizedProducts.add(products.get(possibleIndices.get(0)));
                        productsCopy.clear();
                    }
                }
            default:
                break;
        }
        return prioritizedProducts;
    }

    public static double getJaccardFitnessSum(double[][] distancesMatrix, int max) {
        double sum = 0;
        for (int i = 0; i < max; i++) {
            for (int j = 0; j < max; j++) {
                if (j > i) {
                    sum += distancesMatrix[i][j];
                }
            }
        }
        return sum;
    }

    public static double getJaccardFitnessSum(List<Product> products) {
        double sum = 0;
        int size = products.size();
        for (int i = 0; i < size; i++) {
            for (int j = 0; j < size; j++) {
                if (j > i) {
                    sum += DistancesUtil.getJaccardDistance(products.get(i), products.get(j));
                }
            }
        }
        return sum;
    }

    public static double getBinaryDistance(List<Product> products) {
        double sum = 0;
        int size = products.size();
        for (int i = 0; i < size; i++) {
            for (int j = 0; j < size; j++) {
                if (j > i) {
                    sum += DistancesUtil.getDiffPairs(products.get(i), products.get(j));
                }
            }
        }
        return sum;
    }
}