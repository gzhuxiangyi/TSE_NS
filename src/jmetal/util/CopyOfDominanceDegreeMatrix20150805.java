//  DominanceDegreeMatix.java
//
//  Author:
//      Yi Xiang
//


package jmetal.util;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import jmetal.core.Problem;
import jmetal.core.Solution;
import jmetal.core.SolutionSet;
import jmetal.myutils.QSort;

/**
 * This class implements some facilities for dominance degree matrix. 
 */
public class CopyOfDominanceDegreeMatrix20150805 {
	/**
	* The problem to be solved
	*/
  private Problem problem_;
  
	/**
   * The <code>SolutionSet</code> 
   */
  private SolutionSet   solutionSet_ ;
  
  /**
   * Store the  Dominance degree matrix
   */
  private int [][] domDegreeMat_;
  
  /**
   * Store the objective function 
   */
  private double [][] F_;
  
  /**
   * Store the fitness value 
   */
  private double [] fitness_;
  
  /**
   * An array containing all the fronts found during the search
   */
  private SolutionSet[] ranking_  ;  

  public static  int [] index_;
    
  /** 
   * Constructor.
   * @param solutionSet The <code>SolutionSet</code> to be ranked.
   */       
  public CopyOfDominanceDegreeMatrix20150805(Problem problem, SolutionSet solutionSet) {    
	problem_ =   problem;
    solutionSet_ = solutionSet ; 
    
    index_ = new int  [solutionSet.size()] ;
    
    for(int k = 0; k < solutionSet.size(); k ++){
    	index_[k] = k;
	}
    
    ConstructDDMatrix();   
    
    dominanceDegreeFitness();
  } // DominanceDegreeMatix

  /**
	 * Construct/update dominance degree matrix
	 */
	public void ConstructDDMatrix (){
		int m = problem_.getNumberOfObjectives(); // The number of objectives
		int N = solutionSet_.size(); // The number of individuals
		
		int [][] D = new int [N][N];
		
		/**
		 * Step 1. Construct Y matrix
		 */
		double [][] Y = new double [m][N];
		
		for (int i = 0;i < N; i ++) {
			Solution indi  = solutionSet_.get(i); // Get the ith solution
			
			for (int j = 0; j < m; j++){
				Y[j][i] = indi.getObjective(j);				
			}//for	
			
		}// for i
				
		F_ = Y;		

		
		/**
		 * Step 2. Construct C matrix for each row
		 */
		QSort qSort = new QSort();
		
		for (int i = 0;i < m ;i++) { // For the ith row
			
			double [] w = new double [N]; // Store each row of Y
			
			System.arraycopy(Y[i], 0, w, 0, N);
		
			int [] b = new int [N]; // index	

			System.arraycopy(index_, 0, b, 0, N);			
			
			qSort.quicksort(w, b, 0, N-1);
			
			int [][] C = new int [N][N];
			
			for (int h = 0; h < N; h ++ ) {
				for (int k = h; k < N; k ++) {
					C[b[h]][b[k]] = 1;
				}
			}
			
			/**
			 * Step 3.  Cumsum, i.e., D = D + C
			 */
			for (int r = 0; r < N; r ++) {
				
				for (int k = 0; k < N; k ++) {
					D[r][k] = D[r][k]  + C[r][k];
				}
				
			} // for r
			
		} // for i
		
		
		/**
		 * Step 4. Assign D to domDegreeMat_
		 */
		
		domDegreeMat_ = D;		

	} // ConstructDDMatrix

	
	/**
	 *  This method is used to implement the fast nondominated sorting based on dominance degree matrix
	 * @param D, Dominance degree matrix
	 */
	public void FastNondominatedSorting () {
		int  N = domDegreeMat_[0].length; // The conloms of domDegreeMat_
		int  m = problem_.getNumberOfObjectives();	// The number of Objectives 
		
		int [][] ddMat = new int [N][N];
		
		List<Integer> [] subFronts = new List[N];;
		
		 // Initialize the fronts 
	    for (int i = 0; i < subFronts.length; i++)
	    	subFronts[i] = new LinkedList<Integer>();        
		

		// ddMat is a copy of domDegreeMat_
		for (int i = 0;i < N; i++){
			for(int j = 0;j < N; j++){
				ddMat [i][j] = domDegreeMat_ [i][j];		
				if (i==j) {
					ddMat [i][j] = 0;
				}
//				System.out.print(ddMat [i][j] + " ");
			}		
//			System.out.print("\n");
		}	// for	
		
		
		int [] maxOfCol = new int[N];
		boolean flag = true;
		int frontIdx = 0;
		int times = 0;
		boolean [] removed = new boolean [N];// indicate if a solution is removed
		
		while (flag) {			
			
			// Find the max value of each column
			for (int k = 0; k < N; k++) {
				maxOfCol[k] = Integer.MIN_VALUE;
			}		
		
			
			for (int k = 0; k < N; k++) { // for each column of ddMat
				
				if (removed[k]== true) {
					maxOfCol[k] = -1;
					continue;
				} else {
					
					for (int i = 0; i< N; i ++) {
						
						if (removed[i]== true) {
							continue;
						} else {
							if(ddMat[i][k] > maxOfCol[k]) {
								maxOfCol[k] = ddMat[i][k];
							}
						}
					} // for i
					
				}//if		

			} // for k		
			
			
			// The termination condition, the sum of maxOfCol is equal to -N
			int sum = 0;
			for (int k = 0; k < N; k++){
				sum = sum + maxOfCol[k] ;
			}
			
		    if (sum == -N) {
		    	flag = false;
		    	continue;
		    }	
	
			
			for (int k = 0;k < N; k++) {
				
				if(maxOfCol[k] < m && maxOfCol[k] > -1 ) { 
					
					subFronts[frontIdx].add(k);	
					// Remove the k th row and colomne		
					removed[k] = true;
					
				} //if
				
			}// for k
			
			frontIdx ++ ;
		   
		}// while flag
		
		Iterator<Integer> it1; // Iterators
		
		// Display
//		int i = 0;	
//		while (subFronts[i].size()!= 0 && i <= N-1) {
//			 i++;
//			 it1 = subFronts[i-1].iterator();
//			  
//		      while (it1.hasNext()) {
//		    		System.out.print(it1.next()+"--");
//		      }		      
//		      System.out.println("\n");
//		}				
		
	    ranking_ = new SolutionSet[frontIdx];
	    //0,1,2,....,i-1 are front, then i fronts
	    for (int j = 0; j < frontIdx; j++) {
	      ranking_[j] = new SolutionSet(subFronts[j].size());	      
	      it1 = subFronts[j].iterator();
	      while (it1.hasNext()) {
	    	   Solution sol = solutionSet_.get(it1.next());
	    	   sol.setRank(j);
	           ranking_[j].add(sol);	           
	      }
	    }//for j	    
	    
	} // FastNondominatedSorting
	
/**
 * The fitness assignment of each solution
 * @return
 */
	public void dominanceDegreeFitness (){
		int N = domDegreeMat_[0].length;
		int  m = problem_.getNumberOfObjectives();	// The number of Objectives 
		double [] fitness = new double [N];
		
		/**
		 * Method 1
		 */
		for (int i=0; i< N; i++ ) {
			int counter1 = 0;
			int counter2 = 0;
			int sum = 0;
			
			for(int j=0; j< N;j++) {
				if (j!=i && domDegreeMat_[j][i] == m) {
					counter1 ++;
				}
				
				if (domDegreeMat_[j][i] != m) {
					sum = sum + domDegreeMat_[j][i];
					counter2 ++;
				}
			}// for j	
			
			int dc = counter1;
			double ds ;
			
			if (counter2 == 0) {
				ds = 0.0;
			} else {
				ds = (double)sum/(m*counter2);
			}
			
			fitness [i] = dc + ds;
			solutionSet_.get(i).setFitness(fitness [i]);
		}// for i
			
			
			/**
			 * Method 2
			 */
//		for (int i=0; i< N; i++ ) {
//			    fitness [i] = N;
//			    
//				int counter1 = 0;
//				int counter2 = 0;
//				int sum = 0;
//				// dominate others 
//				for(int j=0; j< N;j++) {
//					if (j!=i && domDegreeMat_[i][j] == m) {
//						counter1 ++;
//					}
//					
//					if (domDegreeMat_[i][j] != m) {
//						sum = sum + domDegreeMat_[i][j];
//						counter2 ++;
//					}
//				}// for j	
//				
//				int dc = counter1;
//				double ds ;
//				
//				if (counter2 == 0) {
//					ds = 0.0;
//				} else {
//					ds = (double)sum/(m*counter2);
//				}
//				
//				fitness [i] = fitness [i] + dc + ds;
//				
//				// dominated by others
//				
//				counter1 = 0;
//				counter2 = 0;
//				sum = 0;
//				
//				for(int j=0; j< N;j++) {
//					if (j!=i && domDegreeMat_[j][i] == m) {
//						counter1 ++;
//					}
//					
//					if (domDegreeMat_[j][i] != m) {
//						sum = sum + domDegreeMat_[j][i];
//						counter2 ++;
//					}
//				}// for j	
//				
//				dc = counter1;			
//				
//				if (counter2 == 0) {
//					ds = 0.0;
//				} else {
//					ds = (double)sum/(m*counter2);
//				}
//				
//				fitness [i] = fitness [i] - dc - ds;				
//				
//				
//			solutionSet_.get(i).setFitness(fitness [i]);
//			
//		} // for i
		
		fitness_ = fitness;		
	}
	
	/**
	 * Select some members according to fitness values
	 * @return
	 */
	public SolutionSet selectMembers (int numbers) {
		SolutionSet selected = new SolutionSet(numbers);
		int N = domDegreeMat_[0].length;
		
		double [] fit = new double [N];
		int [] idx = new int [N];
		
		for  (int k = 0; k < N; k++) {
			idx[k] = k;
		}
		
		System.arraycopy(fitness_, 0, fit , 0, N);
		 
		QSort qSort = new QSort();
		
		qSort.quicksort(fit, idx, 0, N-1);			
			
		for (int i = 0; i <  numbers; i ++) {
			selected.add(solutionSet_.get(idx[i]));	
//			System.out.println(solutionSet_.get(idx[i]).getFitness() + " ");
		}
		
		return selected;
	}
	
	/**
	 * Update minimum neighboring distances using an improved method
	 * 
	 */
	public SolutionSet deleteMinDistanceMember(SolutionSet solutionSet, int numberOfDeleted) {
		int N = solutionSet.size();
		int  m = problem_.getNumberOfObjectives();	// The number of Objectives 				

		
		double [][] F = new double [m][N];
		double [][] A = new double [m][N];
		int [][] B = new int [m][N];
		int [][] C = new int [m][N];
		double [][] D = new double [m][N];
		
		double [] f = new double [N];
		double [] a = new double [N];
		int [] b = new int [N];
		int [] c = new int [N];
		double [] d = new double [N];
		double [] finalD= new double [N];		
		double [] e = new double [N];		
		int [] g = new int [N];		

		
		QSort qSort = new QSort();
		
		/** 
		 *  Step 1. Construct F matrix
		 */
		for (int i = 0;i < N; i ++) {
			Solution indi  = solutionSet.get(i); // Get the ith solution
				
			for (int j = 0; j < m; j++){
				F[j][i] = indi.getObjective(j);		

			}//for	
					
		}// for i
		
		/**
		 * Step 2. Construct A,B,C,D matrix
		 */	
				
		for (int i = 0;i < m; i ++) {
			
			/**
			 *  Construct f vector
			 */				
			// Get the ith row of F
			System.arraycopy(F[i], 0, f, 0, N);		
			
			/**
			 *  Construct a and b vectors
			 */		
		
			System.arraycopy(f, 0, a, 0, N);			
			System.arraycopy(index_, 0, b, 0, N);
			qSort.quicksort(a, b, 0, N-1);	

			/** 
			 * Construct c vector
			 */		
			
			for(int k = 0; k < N; k ++){
				c[b[k]] = k;
			}
			
			/**
			 * Construct d vector
			 */						
			for (int k = 0;k < N; k++) {
				if (c[k] == 0 ||c[k] == N - 1) {
					d[k] = Double.POSITIVE_INFINITY;					
				} else {
//					d[k] = Math.min(a[c[k]+ 1] - a[c[k]], a[c[k]] - a[c[k]-1]) / (a[N-1] - a [0]) ;							
					d[k] = Math.min(a[c[k]+ 1] - a[c[k]], a[c[k]] - a[c[k]-1])  / (a[N-1] - a [0]) 
							+ (a[c[k]+ 1] - a[c[k] - 1]) / (a[N-1] - a [0]) ;
//					d[k] = (a[c[k]+ 1] - a[c[k] - 1]) / (a[N-1] - a [0])  ;
				}
//				System.out.println("d[k] = " + d[k]);
			}// for k			
	
			
			/**
			 * Assign a,b,c,d to each row of A,B,C,D
			 */			
			System.arraycopy(a, 0, A[i], 0, N);
			System.arraycopy(b, 0, B[i], 0, N);
			System.arraycopy(c, 0, C[i], 0, N);
			System.arraycopy(d, 0, D[i], 0, N);			
		} // for i
		
		/**
		 * 	Construct finalD vector
		 */
		for (int j = 0; j < N; j++) {
            // sum 			
//			finalD[j] =0.0;			
//			for (int i = 0; i< m; i++) {
//				if (D[i][j] == Double.POSITIVE_INFINITY) {
//					finalD[j] = Double.POSITIVE_INFINITY;
//					break;
//				} else {
//					finalD[j] = finalD[j] + D[i][j];
//				}
//			}
			// product
			finalD[j] = 1.0;			
			for (int i = 0; i < m; i++) {
				if (D[i][j] == Double.POSITIVE_INFINITY) {
					finalD[j] = Double.POSITIVE_INFINITY;
					break;
				} else {
					finalD[j] = finalD[j] * D[i][j];
				}
			}			

			// min
//			finalD[j] = Double.POSITIVE_INFINITY;
//			
//			for (int i = 0; i < m; i++) {
//				if (D[i][j] <  finalD[j]) {
//					finalD[j] = D[i][j];
//				}
//				
//			}
			
			solutionSet.get(j).setCrowdingDistance(finalD[j]);
		}
		/**
		 * Construct e and g vectors
		 */
//		System.arraycopy(finalD, 0, e, 0, N);
//		System.arraycopy(index_, 0, g, 0, N);
//		qSort.quicksort(e, g, 0, N-1);	
		
		 /**
		  * Update F,A,B,C,D
		  */
		
		for (int n = 0;n < numberOfDeleted; n++ ) {	
			
			int k = minFastSort(finalD,N); // the index in F to be deleted	
//			int k = g[0];
			
//			//delete the first element in e
//			deleteElemet(e, 0, N);
//			
//			//delete the first element in g, and update g			
//			for (int h=1; h < N;h++) {
//				if (g[h] > k) {
//					g[h] = g[h] - 1;
//				}
//				g[h-1] = g[h];
//			}
			
			// delete the kth element in finalD
			deleteElemet(finalD, k, N);
			
			// delete the kth element in  solutionSet
			solutionSet.remove(k);
			
			for (int i = 0;i < m;i++) {		
				f = F[i];
				a = A[i];
				b = B[i];
				c = C[i];
				d = D[i];				

				int ck = c[k];// the index in a to be deleted					
				double rang = a[N-1] - a[0];
				
				/**
				 * Update f and a
				 * 
				 */
				deleteElemet(f, k, N);
				deleteElemet(a, ck, N);				
				
				/**
				 * Update c1 
				 */
				int [] c1 = new int[N];				
				
				// calculate c1
				for (int j = 0; j < N; j++) {
					if (j <= ck) {
						c1[b[j]] = c[b[j]];
					} else {
						c1[b[j]] = c[b[j]] - 1;
					}
				}						
					
				
				/**
				 * Update b1
				 */
				int [] b1 = new int[N];
				
				for (int j=0; j < N; j++) {
					if (j <= k) {
						b1[c[j]] = b[c[j]];
					} else {
						b1[c[j]] = b[c[j]] - 1;
					}
				}
				

				/**
				 * Delete  the kth element in c1 and the c(k)th element in b1 respectively
				 */	
				
				deleteElemet(c1, k, N);				
				deleteElemet(b1, ck, N);
				System.arraycopy(c1, 0, c, 0, N-1);
				System.arraycopy(b1, 0, b, 0, N-1);			
				
				/**
				 * Update d and finalD
				 */
				
				deleteElemet(d, k, N);	
				
				// Update the b[c(k)-1] and b[c(k)] in d	
				
				int idx1 = 0,idx2 = 0;		
				double d1 = 0.0,d2 = 0.0;				
				/**
				 * ///////////////////////////The original codes//////////////////////
				 */
				if (ck==0 || ck == N - 1) {
					if (ck == 0) {
						idx2 = b[ck];	
						idx1 = -1;
						d2 = d[idx2];
						d[idx2] = Double.POSITIVE_INFINITY;
					}
					
					if (ck == N-1) { 
						idx1 = b[ck-1];
						idx2 = -1;
						d1 = d[idx1];
						d[idx1] = Double.POSITIVE_INFINITY;
					}
				} else {
					
					idx1 = b[ck-1];
					if (c[idx1] == 0 ||c[idx1] == N - 2) {
						d1 = d[idx1];
						d[idx1] = Double.POSITIVE_INFINITY;
					} else {
						d1 = d[idx1];
						d[idx1] = Math.min(a[c[idx1]+ 1] - a[c[idx1]], a[c[idx1]] - a[c[idx1]-1]) /rang
								+ (a[c[idx1]+ 1] - a[c[idx1] - 1]) /rang;
						
//						d[idx1] = (a[c[idx1]+ 1] - a[c[idx1] - 1]) /rang;
					}	
					
					idx2 = b[ck];				
					
					if (c[idx2] == 0 ||c[idx2] == N - 2) {
						d2 = d[idx2];
						d[idx2] = Double.POSITIVE_INFINITY;
					} else {
						d2 = d[idx2];
						d[idx2] = Math.min(a[c[idx2]+ 1] - a[c[idx2]], a[c[idx2]] - a[c[idx2]-1])  /rang
								+ (a[c[idx2]+ 1] - a[c[idx2] - 1]) /rang;
						
//						d[idx2] = (a[c[idx2]+ 1] - a[c[idx2] - 1]) /rang;
					}			
				}
				
				// Update finalD
				
				if (idx1 != -1) {
					if (d1 != 0.0 && d1 != Double.POSITIVE_INFINITY) {
						finalD[idx1] = finalD[idx1]/d1 * d[idx1]; 
					} else {
						finalD[idx1] = d1;
					}
					
					solutionSet.get(idx1).setCrowdingDistance(finalD[idx1]);
				} // if dix1
			
				
				if (idx2 != -1) {
					if (d2 != 0.0 && d2 != Double.POSITIVE_INFINITY) {
						finalD[idx2] = finalD[idx2]/d2 * d[idx2]; 
					} else {
						finalD[idx2] = d2;
					}
					
					solutionSet.get(idx2).setCrowdingDistance(finalD[idx2]);
				} // if dix2				
								
				/**
				 * update finalD use binary search
				 */	
				
			} // for i			
			N --;		
		}// for n
		
		return solutionSet;
	}
	
	
	/**
	 * Update minimum neighboring distances using arrays
	 * 
	 */
	public SolutionSet updateMinDistanceMember(SolutionSet solutionSet, int numberOfDeleted) {
		int N = solutionSet.size();
		int  m = problem_.getNumberOfObjectives();	// The number of Objectives 
		
		
		double [][] F = new double [m][N];
		double [][] A = new double [m][N];
		int [][] B = new int [m][N];
		int [][] C = new int [m][N];
		double [][] D = new double [m][N];
		
		double [] f = new double [N];
		double [] a = new double [N];
		int [] b = new int [N];
		int [] c = new int [N];
		double [] d = new double [N];
		double [] finalD= new double [N];		
		double [] e = new double [N];		
		int [] g = new int [N];		
		
		QSort qSort = new QSort();
		
		/** 
		 *  Step 1. Construct F matrix
		 */
		for (int i = 0;i < N; i ++) {
			Solution indi  = solutionSet.get(i); // Get the ith solution
				
			for (int j = 0; j < m; j++){
				F[j][i] = indi.getObjective(j);				
			}//for	
					
		}// for i
		
		/**
		 * Step 2. Construct A,B,C,D matrix
		 */	
				
		for (int i = 0;i < m; i ++) {
			
			/**
			 *  Construct f vector
			 */				
			// Get the ith row of F
			System.arraycopy(F[i], 0, f, 0, N);		
			
			/**
			 *  Construct a and b vectors
			 */		
		
			System.arraycopy(f, 0, a, 0, N);			
			System.arraycopy(index_, 0, b, 0, N);
			qSort.quicksort(a, b, 0, N-1);	

			/** 
			 * Construct c vector
			 */		
			
			for(int k = 0; k < N; k ++){
				c[b[k]] = k;
			}
			
			/**
			 * Construct d vector
			 */						
			for (int k = 0;k < N; k++) {
				if (c[k] == 0 ||c[k] == N - 1) {
					d[k] = Double.POSITIVE_INFINITY;					
				} else {
//					d[k] = Math.min(a[c[k]+ 1] - a[c[k]], a[c[k]] - a[c[k]-1]) / (a[N-1] - a [0]) ;							
					d[k] = Math.min(a[c[k]+ 1] - a[c[k]], a[c[k]] - a[c[k]-1])  / (a[N-1] - a [0]) 
							+ (a[c[k]+ 1] - a[c[k] - 1]) / (a[N-1] - a [0]) ;
//					d[k] = (a[c[k]+ 1] - a[c[k] - 1]) / (a[N-1] - a [0])  ;
				}
//				System.out.println("d[k] = " + d[k]);
			}// for k			
	
			
			/**
			 * Assign a,b,c,d to each row of A,B,C,D
			 */			
			System.arraycopy(a, 0, A[i], 0, N);
			System.arraycopy(b, 0, B[i], 0, N);
			System.arraycopy(c, 0, C[i], 0, N);
			System.arraycopy(d, 0, D[i], 0, N);			
		} // for i
		
		/**
		 * 	Construct finalD vector
		 */
		for (int j = 0; j < N; j++) {
            // sum 			
//			finalD[j] =0.0;			
//			for (int i = 0; i< m; i++) {
//				if (D[i][j] == Double.POSITIVE_INFINITY) {
//					finalD[j] = Double.POSITIVE_INFINITY;
//					break;
//				} else {
//					finalD[j] = finalD[j] + D[i][j];
//				}
//			}
			// product
			finalD[j] = 1.0;			
			for (int i = 0; i < m; i++) {
				if (D[i][j] == Double.POSITIVE_INFINITY) {
					finalD[j] = Double.POSITIVE_INFINITY;
					break;
				} else {
					finalD[j] = finalD[j] * D[i][j];
				}
			}			

			// min
//			finalD[j] = Double.POSITIVE_INFINITY;
//			
//			for (int i = 0; i < m; i++) {
//				if (D[i][j] <  finalD[j]) {
//					finalD[j] = D[i][j];
//				}
//				
//			}
			
			solutionSet.get(j).setCrowdingDistance(finalD[j]);
		}
		/**
		 * Construct e and g vectors
		 */
//		System.arraycopy(finalD, 0, e, 0, N);
//		System.arraycopy(index_, 0, g, 0, N);
//		qSort.quicksort(e, g, 0, N-1);	
		
		 /**
		  * Update F,A,B,C,D
		  */
		
		for (int n = 0;n < numberOfDeleted; n++ ) {	
			
			int k = minFastSort(finalD,N); // the index in F to be deleted	
//			int k = g[0];
			
//			//delete the first element in e
//			deleteElemet(e, 0, N);
//			
//			//delete the first element in g, and update g			
//			for (int h=1; h < N;h++) {
//				if (g[h] > k) {
//					g[h] = g[h] - 1;
//				}
//				g[h-1] = g[h];
//			}
			
			// delete the kth element in finalD
			deleteElemet(finalD, k, N);
			
			// delete the kth element in  solutionSet
			solutionSet.remove(k);
			
			for (int i = 0;i < m;i++) {		
				f = F[i];
				a = A[i];
				b = B[i];
				c = C[i];
				d = D[i];				

				int ck = c[k];// the index in a to be deleted					
				double rang = a[N-1] - a[0];
				
				/**
				 * Update f and a
				 * 
				 */
				deleteElemet(f, k, N);
				deleteElemet(a, ck, N);				
				
				/**
				 * Update c1 
				 */
				int [] c1 = new int[N];				
				
				// calculate c1
				for (int j = 0; j < N; j++) {
					if (j <= ck) {
						c1[b[j]] = c[b[j]];
					} else {
						c1[b[j]] = c[b[j]] - 1;
					}
				}						
					
				
				/**
				 * Update b1
				 */
				int [] b1 = new int[N];
				
				for (int j=0; j < N; j++) {
					if (j <= k) {
						b1[c[j]] = b[c[j]];
					} else {
						b1[c[j]] = b[c[j]] - 1;
					}
				}
				

				/**
				 * Delete  the kth element in c1 and the c(k)th element in b1 respectively
				 */	
				
				deleteElemet(c1, k, N);				
				deleteElemet(b1, ck, N);
				System.arraycopy(c1, 0, c, 0, N-1);
				System.arraycopy(b1, 0, b, 0, N-1);			
				
				/**
				 * Update d and finalD
				 */
				
				deleteElemet(d, k, N);	
				
				// Update the b[c(k)-1] and b[c(k)] in d	
				
				int idx1 = 0,idx2 = 0;		
				double d1 = 0.0,d2 = 0.0;				
				/**
				 * ///////////////////////////The original codes//////////////////////
				 */
				if (ck==0 || ck == N - 1) {
					if (ck == 0) {
						idx2 = b[ck];	
						idx1 = -1;
						d2 = d[idx2];
						d[idx2] = Double.POSITIVE_INFINITY;
					}
					
					if (ck == N-1) { 
						idx1 = b[ck-1];
						idx2 = -1;
						d1 = d[idx1];
						d[idx1] = Double.POSITIVE_INFINITY;
					}
				} else {
					
					idx1 = b[ck-1];
					if (c[idx1] == 0 ||c[idx1] == N - 2) {
						d1 = d[idx1];
						d[idx1] = Double.POSITIVE_INFINITY;
					} else {
						d1 = d[idx1];
						d[idx1] = Math.min(a[c[idx1]+ 1] - a[c[idx1]], a[c[idx1]] - a[c[idx1]-1]) /rang
								+ (a[c[idx1]+ 1] - a[c[idx1] - 1]) /rang;
						
//						d[idx1] = (a[c[idx1]+ 1] - a[c[idx1] - 1]) /rang;
					}	
					
					idx2 = b[ck];				
					
					if (c[idx2] == 0 ||c[idx2] == N - 2) {
						d2 = d[idx2];
						d[idx2] = Double.POSITIVE_INFINITY;
					} else {
						d2 = d[idx2];
						d[idx2] = Math.min(a[c[idx2]+ 1] - a[c[idx2]], a[c[idx2]] - a[c[idx2]-1])  /rang
								+ (a[c[idx2]+ 1] - a[c[idx2] - 1]) /rang;
						
//						d[idx2] = (a[c[idx2]+ 1] - a[c[idx2] - 1]) /rang;
					}			
				}
				
				// Update finalD
				
				if (idx1 != -1) {
					if (d1 != 0.0 && d1 != Double.POSITIVE_INFINITY) {
						finalD[idx1] = finalD[idx1]/d1 * d[idx1]; 
					} else {
						finalD[idx1] = d1;
					}
					
					solutionSet.get(idx1).setCrowdingDistance(finalD[idx1]);
				} // if dix1
			
				
				if (idx2 != -1) {
					if (d2 != 0.0 && d2 != Double.POSITIVE_INFINITY) {
						finalD[idx2] = finalD[idx2]/d2 * d[idx2]; 
					} else {
						finalD[idx2] = d2;
					}
					
					solutionSet.get(idx2).setCrowdingDistance(finalD[idx2]);
				} // if dix2				
								
				/**
				 * update finalD use binary search
				 */	
				
			} // for i			
			N --;		
		}// for n
		
		return solutionSet;
	}
/**
   * Returns a <code>SolutionSet</code> containing the solutions of a given rank. 
   * @param rank The rank
   * @return Object representing the <code>SolutionSet</code>.
   */
  public SolutionSet getSubfront(int rank) {
    return ranking_[rank];
  } // getSubFront

  /** 
  * Returns the total number of subFronts founds.
  */
  public int getNumberOfSubfronts() {
    return ranking_.length;
  } // getNumberOfSubfronts
  
   public int[][] getDomDegreeMat() {
		return domDegreeMat_;
	}

	public void setDomDegreeMat(int[][] domDegreeMat) {
		this.domDegreeMat_ = domDegreeMat;
	}
	/**
	 * Delete the an element in a specified by index
	 * @param a
	 * @param index
	 */
	public void deleteElemet(int [] a, int index, int length) {
		for (int i = index + 1; i < length; i++) {
			a[i-1] = a[i];
		}
	}
	/**
	 * Find the minimum value in an array
	 */
	  public int minFastSort(double x[], int n) {		  
	      int idx = 0;
	      for (int j = 1; j < n; j++) {
	        if (x[j] < x[idx]) {
	             idx = j;
	        } // if
	      }
		   return idx;
	  } // minFastSort
	
	/**
	 * Delete the an element in a specified by index
	 * @param a
	 * @param index
	 */
	public void deleteElemet(double [] a, int index,int length) {
		for (int i = index + 1; i < length; i++) {
			a[i-1] = a[i];
		}
//		System.out.println("here");
//		System.arraycopy(a, index+1, a, index, length - index - 1);
	}
} // DominanceDegreeMatix
