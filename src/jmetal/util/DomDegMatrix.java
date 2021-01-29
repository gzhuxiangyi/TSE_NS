/**  DomDegMatix.java
// This class uses matrix to select and delete members in EAs,
//  Author:
//      Yi Xiang 
//  
*/

package jmetal.util;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import jmetal.core.Problem;
import jmetal.core.Solution;
import jmetal.core.SolutionSet;
import jmetal.myutils.QSort;
import Jama.Matrix;

/**
 * This class implements some facilities for dominance degree matrix. 
 */
public class DomDegMatrix {
	/**
	* The problem to be solved
	*/
  private Problem problem_;
  
	/**
   * The <code>SolutionSet</code> 
   */
  private SolutionSet   solutionSet_ ;
  
  private Solution offspring_;
  private int M_; // The number of objectives
  
  private int N_; // The number of solutions in solutionSet_
 
  private double[][] F_;

  /**
   * Store the  Dominance degree matrix
   */
  private int [][] domDegreeMat_;  
  
  /**
   * Store the fitness value 
   */
  private double [] fitness_;
  
  /**
   * An array containing all the fronts found during the search
   */
  private SolutionSet[] ranking_  ;  
  /**
   * Contain the index of solutions in each front
   */
  private List<Integer> [] subFronts_;
  
  private int frontNumber_;

  public static  int [] index_;
    
  /** 
   * Constructor.
   * @param solutionSet The <code>SolutionSet</code> to be ranked.
   */       
  public DomDegMatrix(Problem problem, SolutionSet solutionSet) {    
	problem_ =   problem;
	solutionSet_ = solutionSet ; 
	
	M_ = problem_.getNumberOfObjectives();     
    N_ = solutionSet_.size();  
	
//	// for test
//	M_ = 3;      
//    N_ = 6;     
    
    domDegreeMat_ = new int [N_ + 1][ N_ + 1];
    F_ = new  double [M_][ N_ + 1];

    fitness_ = new double [N_ + 1];
    
    index_ = new int  [N_] ;
    
    for(int k = 0; k < N_; k ++){
    	index_[k] = k;
	}   
    
    ConstructDDMatrix();
    FastNondominatedSorting();
    crowdingDistanceAssignmentAll();
  } // DomDegMatix

  /**
	 * Construct/update dominance degree matrix
	 */
	public void ConstructDDMatrix (){		
		/**
		 * Step 1. Construct objective matrix F_
		 */				
		for (int i = 0;i < N_; i ++) {
			Solution indi  = solutionSet_.get(i); // Get the ith solution			
			
			for (int j = 0; j < M_; j++){
				F_[j][i] = indi.getObjective(j);	
			}//for	
			
		}// for i
		
		/**
		 * Step 2. Construct C matrix for each row
		 */			
		
		for (int i = 0;i < M_ ;i++) { // For the ith row
			
			int [][] C = new int [N_ + 1][N_ + 1];
			
			double [] a = new double [N_];
			int [] b = new int [N_];
			
			System.arraycopy(F_[i], 0, a, 0, N_);		
			System.arraycopy(index_, 0, b, 0, N_);				
						
			Utils.QuickSort(a, b, 0, N_ - 1);
//			QSort.quicksort(a, b, 0, N_- 1);
			
			for (int h = 0; h < N_; h ++ ) {
				for (int k = h; k < N_; k ++) {
					C[b[h]][b[k]] = 1;
				}
			}		
			
			/**
			 * Step 3.  accumulation, i.e., domDegreeMat_ = domDegreeMat_ + C
			 */
			for (int r = 0; r < N_ + 1; r ++) {
				
				for (int k = 0; k < N_ + 1; k ++) {
					domDegreeMat_[r][k] = domDegreeMat_[r][k]  + C[r][k];
				}
				
			} // for r

		} // for i	

	} // ConstructDDMatrix	
	
	 /**
		 * Construct/update dominance degree matrix
		 */
		public void ConstructDDMatrix (double [][] F){		
			/**
			 * Step 1. Construct objective matrix F_
			 */				
			F_ = F;
			
			/**
			 * Step 2. Construct C matrix for each row
			 */			
			
			for (int i = 0;i < M_ ;i++) { // For the ith row
				
				int [][] C = new int [N_ + 1][N_ + 1];
				
				double [] a = new double [N_];
				int [] b = new int [N_];
				
				System.arraycopy(F_[i], 0, a, 0, N_);		
				System.arraycopy(index_, 0, b, 0, N_);				
							
//				Utils.QuickSort(a, b, 0, N_- 1);
				QSort.quicksort(a, b, 0, N_- 1);
				
				for (int h = 0; h < N_; h ++ ) {
					for (int k = h; k < N_; k ++) {
						C[b[h]][b[k]] = 1;
					}
				}		
				
				/**
				 * Step 3.  accumulation, i.e., domDegreeMat_ = domDegreeMat_ + C
				 */
				for (int r = 0; r < N_ + 1; r ++) {
					
					for (int k = 0; k < N_ + 1; k ++) {
						domDegreeMat_[r][k] = domDegreeMat_[r][k]  + C[r][k];
					}
					
				} // for r

			} // for i	
           
			// print
			System.out.println("*******************Dominance degree matrix****************");
			for (int r = 0; r < N_ + 1; r ++) {
				
				for (int k = 0; k < N_ + 1; k ++) {
					System.out.print(domDegreeMat_[r][k] + " "); 
				}
				System.out.println(" \n "); 
			} // for r
	
		} // ConstructDDMatrix	
	
		
		/**
		 *  This method is used to implement the fast nondominated sorting based on dominance degree matrix
		 * @param D, Dominance degree matrix
		 */
		public void FastNondominatedSorting () {
					
			int [][] ddMat = new int [N_][N_];
			
			List<Integer> [] subFronts = new List[N_];
			
			 // Initialize the fronts 
		    for (int i = 0; i < subFronts.length; i++)
		    	subFronts[i] = new LinkedList<Integer>();        
			

			// ddMat is a copy of domDegreeMat_
			for (int i = 0;i < N_; i++){
				for(int j = 0;j < N_; j++){
					ddMat [i][j] = domDegreeMat_ [i][j];		
					if (i==j) {
						ddMat [i][j] = 0;
					}
//					System.out.print(ddMat [i][j] + " ");
				}		
//				System.out.print("\n");
			}	// for	
			
			
			int [] maxOfCol = new int[N_];
			boolean flag = true;
			int frontIdx = 0;
			boolean [] removed = new boolean [N_];// indicate if a solution is removed
			
			while (flag) {			
				
				// Find the max value of each column
				for (int k = 0; k < N_; k++) {
					maxOfCol[k] = Integer.MIN_VALUE;
				}		
			
				
				for (int k = 0; k < N_; k++) { // for each column of ddMat
					
					if (removed[k]== true) {
						maxOfCol[k] = -1;
						continue;
					} else {
						
						for (int i = 0; i< N_; i ++) {
							
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
				for (int k = 0; k < N_; k++){
					sum = sum + maxOfCol[k] ;
				}
				
			    if (sum == -N_) {
			    	flag = false;
			    	continue;
			    }	
		
				
				for (int k = 0;k < N_; k++) {
					
					if(maxOfCol[k] < M_ && maxOfCol[k] > -1 ) { 
						
						subFronts[frontIdx].add(k);	
						// Remove the k th row and colomne		
						removed[k] = true;
						
					} //if
					
				}// for k
				
				frontIdx ++ ;
			   
			}// while flag
			
			Iterator<Integer> it1; // Iterators			
			
			frontNumber_ = frontIdx;
			subFronts_ = new List[frontNumber_]; 
		    //0,1,2,....,i-1 are front, then i fronts
		    for (int j = 0; j < frontNumber_; j++) {
		      subFronts_[j] = new LinkedList<Integer>(); 
		      it1 = subFronts[j].iterator();
		      while (it1.hasNext()) {
		    	   int index = it1.next();
//		    	   Solution sol = solutionSet_.get(index);
//		    	   sol.setRank(j);
		    	   subFronts_[j].add(index);	           
		      }
		    }//for j	
		    
//			// Display
//		    System.out.println("*******************Fast sorting results****************");
//			int i = 0;	
//			for (i=0; i < subFronts_.length;i++){
//				 it1 = subFronts[i].iterator();
//				  
//			      while (it1.hasNext()) {
//			    		System.out.print(it1.next()+"--");
//			      }		      
//			      System.out.println("\n");
//			}	
		} // FastNondominatedSorting
		
	/** 
	 * Assign crowding distance to all front	
	 */
	public void	crowdingDistanceAssignmentAll	() {
		for (int front = 0; front < frontNumber_; front ++) {
			crowdingDistanceAssignment (front) ;
		}// for front
	}
			
		
	/** 
	 * Assign crowding distance to a front	
	 */
	public void	crowdingDistanceAssignment (int front) {
			
//			System.out.println("The front " + front);
			
			int frontSize = subFronts_[front].size();
			int [] id = new int[frontSize];// the ID of solutions in this front
			
			for (int i=0;i<frontSize;i++) {
				id[i] = subFronts_[front].get(i);
			}
						
			double [][] D = new double [M_][frontSize];
			double [] cd = new double [frontSize];
			
			for (int m = 0; m < M_; m ++){
				
				double  [] f = new double [frontSize];
				int  [] b = new int [frontSize];
				int [] c = new int [frontSize];
				
				// initilize b vector
				for (int k =0;k < frontSize;k++ ){
					b[k] = k;
				}
				
				// construct f vector
				for (int i=0; i < frontSize;i++) {
					f[i] = F_[m][id[i]];					
				}
				
//				Utils.QuickSort(f, b, 0, frontSize - 1);
				if (frontSize > 1)
					QSort.quicksort(f, b, 0, frontSize- 1);
				// construct c vector				
				
				for(int k = 0; k < frontSize; k ++){
					c[b[k]] = k;				
				}
				
//				System.out.println("-- the c in " + m + "th objective");
//				for(int k = 0; k < frontSize; k ++){
//					System.out.print("----" + c[k] + " ");			
//				}
//				System.out.print("\n");		
				
				
				// construct D matrix				
				for(int k = 0; k < frontSize; k ++){
					
					if (c[k] == 0 ||c[k] == frontSize - 1) {
//						D[m][k] = Double.POSITIVE_INFINITY;		
						if (frontSize == 1) {
							D[m][k] = Double.POSITIVE_INFINITY;		
						} else {
							if (c[k] == 0) {
								D[m][k] = (f[c[k]+ 1] - f[c[k]]) / (f[frontSize -1] - f [0]) ;
							} else {
								D[m][k] = ( f[c[k]] - f[c[k]-1]) / (f[frontSize -1] - f [0]) ;
							}
						}
						
					} else {						
						D[m][k] = (f[c[k]+ 1] - f[c[k] - 1]) / (f[frontSize -1] - f [0]) ;
						
//						D[m][k] = Math.min(f[c[k]+ 1] - f[c[k]], f[c[k]] - f[c[k]-1])  / (f[frontSize-1] - f [0]);
//								+ (f[c[k]+ 1] - f[c[k] - 1]) / (f[frontSize -1] - f [0]) ;
					}// if			

				}// for k
//				
//				System.out.println("-- the d in " + m + "th objective");
//				for(int k = 0; k < frontSize; k ++){
//					System.out.print("----" + D[m][k] + " ");			
//				}
//				System.out.print("\n");		
				
			} // for m
			
			// product
			for (int j=0;j < frontSize;j++) {
				cd[j] = 1.0;			
				for (int i = 0; i < M_; i++) {
					if (D[i][j] == Double.POSITIVE_INFINITY) {
						cd[j] = Double.POSITIVE_INFINITY;				
						break;
					} else {
						cd[j] = cd[j] * D[i][j];
					}
				}	
				if (id[j] == N_) {
					offspring_.setCrowdingDistance(cd[j]);
				} else 
					solutionSet_.get(id[j]).setCrowdingDistance(cd[j]);
			}// for 
			
			
			// min
//			for (int j=0;j < frontSize;j++) {
//				cd[j] = Double.POSITIVE_INFINITY;	
//				
//				for (int i = 0; i < M_; i++) {
//					if (D[i][j] <  cd[j]) {
//						cd[j] = D[i][j];
//					}
//					
//				}
//				if (id[j] == N_) {
//					offspring_.setCrowdingDistance(cd[j]);
//				} else 
//					solutionSet_.get(id[j]).setCrowdingDistance(cd[j]);
//			}// for 	
			
			// sum
//			for (int j=0;j < frontSize;j++) {
//				cd[j] =0.0;			
//				for (int i = 0; i< M_; i++) {
//					if (D[i][j] == Double.POSITIVE_INFINITY) {
//						cd[j] = Double.POSITIVE_INFINITY;
//						break;
//					} else {
//						cd[j] = cd[j] + D[i][j];
//					}
//				}
//				if (id[j] == N_) {
//					offspring_.setCrowdingDistance(cd[j]);
//				} else 
//					solutionSet_.get(id[j]).setCrowdingDistance(cd[j]);
//			}// for 	
				
//			System.out.println("-- the cd  " );
//			for(int k = 0; k < frontSize; k ++){
//				System.out.print("----" + cd[k] + " ");			
//			}
//			System.out.print("\n");				

	}// crowdingDistanceAssignment

	/**
	 * Update when adding a solution
	 * @param solution
	 */
	public void addSolution (Solution solution){
		offspring_ = solution;
		// update F_
		updateFWhenAdd(offspring_);
		updateMatrixWhenAdd();
		
	}
	
	public void updateFWhenAdd(Solution solution){
		for (int i=0;i< M_;i++) {
			F_[i][N_] = solution.getObjective(i);
		}
//		System.out.println(F_[0].length);
//		// for test
//		F_[0][N_] = 0.4213;
//		F_[1][N_] = 0.8324;
//		F_[2][N_] = 0.5215;
	}
	
	public void updateFWhenDelete(int solID){
		
       if (solID!= N_) {
    	   // copy the N columne to the solID
    	   for (int i=0;i < M_;i++){
    		   F_[i][solID] = F_[i][N_];
    	   }
    	   solutionSet_.replace(solID, offspring_);   
    	   
    	   // modify the front where the Nth solution at 
    	   int frontID = offspring_.getRank();
    	   
    	   Iterator<Integer> it = subFronts_[frontID].iterator();	  	   
    	   
    	   while(it.hasNext())   {  
	  		     if(it.next() == N_) {  
	  		         it.remove();  
	  		     }  
	  	   }
    	   subFronts_[frontID].add(solID);    	   
    	   
       }// if
	}
	
	public boolean updateMatrixWhenAdd( ){
		
		boolean flag = true;
		
		for (int n = 0; n < N_; n++) {
			flag = false;
			int counter = 0;
			
			for (int i=0;i< M_;i++) {
				if (F_[i][n] <= F_[i][N_]) {
					counter ++;
				}
				if (F_[i][n] != F_[i][N_]) {
					flag = true;
				}
			}// for i
			
			if (flag == true ) {
				domDegreeMat_[n][N_] = counter;
				domDegreeMat_[N_][n] = M_ - counter;
			} else {	
				return flag;				
			}
			
		}// for n
		
		domDegreeMat_[N_][N_] = M_;
		return flag;
//		System.out.println("*******************Dominance degree matrix(new)****************");
//		for (int r = 0; r < N_ + 1; r ++) {
//			
//			for (int k = 0; k < N_ + 1; k ++) {
//				System.out.print(domDegreeMat_[r][k] + " "); 
//			}
//			System.out.println(" \n "); 
//		} // for r
	}
	
	
	public void updateMatrixWhenDelete(int solID){
		
		 if (solID!= N_) {
			 for (int i = 0;i< solID;i++) {
				 domDegreeMat_[i][solID] = domDegreeMat_[i][N_];
				 domDegreeMat_[solID][i] = domDegreeMat_[N_][i];
			 }
			 
			 for (int i = solID + 1;i < N_;i++) {
				 domDegreeMat_[i][solID] = domDegreeMat_[i][N_];
				 domDegreeMat_[solID][i] = domDegreeMat_[N_][i];
			 }
			 
			 domDegreeMat_[solID][solID] = M_;
		 }
	}
	
	
	
	public void updateFrontsWhenAdd( ){
		int maxFront = -1;
		
		for (int i=0; i < N_; i++) {
			if (domDegreeMat_[i][N_] == M_) {
				if (solutionSet_.get(i).getRank() > maxFront){
					maxFront = solutionSet_.get(i).getRank();
				}
			}
		}// for 
		
		int frontToInsert = maxFront + 1;				
		 
		List <Integer> addedSolution = new LinkedList <Integer>();
		addedSolution.add(N_);
		
		while (addedSolution.size() > 0){			
			reallocateFronts(frontToInsert);  
			List <Integer> dominatedBySolutions= new LinkedList <Integer>();
			// Find solutions dominated by Offspring in the frontToInsert-th front
			
			for (int i=0;i < addedSolution.size();i++) {
				int addID = addedSolution.get(i);
				
				Iterator<Integer> it; // Iterator				 
//				System.out.println("frontNumber = " + frontNumber_ );
//				System.out.println("frontToInsert = " + frontToInsert );
				it = subFronts_[frontToInsert].iterator();
				
				while (it.hasNext()) {
		    	   int index = it.next();
		    	   if (domDegreeMat_[addID][index] == M_) { // offspring dominates the index solution
		    		   if (!dominatedBySolutions.contains(index_))
		    			   dominatedBySolutions.add(index);		    		   
		    	   }		    	  
			    }// while
				  
			} // for i
			
			 if (dominatedBySolutions.size() > 0) { 
				 reallocateFronts(frontToInsert);  
				 // delete solutions dominated by offspring in the frontToInsert-th front  	
		    	 for (int i=0; i< dominatedBySolutions.size();i++){
		    		 Iterator<Integer> it = subFronts_[frontToInsert].iterator();
		    		 while(it.hasNext())   {  
		    		     if(it.next() == dominatedBySolutions.get(i)) {  
		    		         it.remove();  
		    		     }  
		    	     }
		         }// for
		    	 
		    	 for (int i = 0; i < addedSolution.size();i++) {
		    		 
		    		 int idx = addedSolution.get(i);
		    		 subFronts_[frontToInsert].add(idx);	
		    		 if (idx == N_) {
		    			offspring_.setRank(frontToInsert);
		    		 } else {
		    			solutionSet_.get(idx).setRank(frontToInsert);
		    		 }			    		 
		    	 }	// for i		
		    	 
//		    	 crowdingDistanceAssignment(frontToInsert);
		    	 addedSolution = dominatedBySolutions; // update to be added Solutions	
		    	 frontToInsert ++;
		    	 
		     } else {// no solutions dominated by offspring
		    	 reallocateFronts(frontToInsert);   
		    	 
		    	 for (int i =0; i< addedSolution.size();i++) {
		    		 
		    		 int idx = addedSolution.get(i);
		    		 subFronts_[frontToInsert].add(idx);	
		    		 if (idx == N_) {
		    			offspring_.setRank(frontToInsert);
		    		 } else {
		    			solutionSet_.get(idx).setRank(frontToInsert);
		    		 }
		    		 
		    	 }	//for
		    	 
//		    	 crowdingDistanceAssignment(frontToInsert);
		    	 addedSolution.clear();
		     }	// if(dominatedBySolutions.size() > 0)			 
			 
		} // while	
	} // 
	
	private void reallocateFronts (int frontToInsert){
		
		 if (frontToInsert >= frontNumber_ ){ // A new front is needed
				
				List<Integer> [] sf = new List [frontNumber_];
				 
				 for (int i = 0;i < frontNumber_; i++) {
					 sf[i] = new LinkedList<Integer>(); 
					 sf[i] = subFronts_[i];
				 }
				 
				 frontNumber_ ++;
				 subFronts_  = new List [frontNumber_];
				 
				 for (int i = 0;i < frontNumber_ - 1;i++) {
					 subFronts_[i] = new LinkedList<Integer>(); 
					 subFronts_[i] = sf[i];
				 }
				 subFronts_[frontNumber_ - 1] = new LinkedList<Integer>(); 
		 }// if
	}
	/**
	 * Delete a solution in frontID
	 */
	public void updateFrontsWhenDelete(int frontID){		
		crowdingDistanceAssignment(frontID);
		Iterator<Integer> it = subFronts_[frontID].iterator();	
		
		double minDis = Double.POSITIVE_INFINITY; 
		int minIdx = -1;
		
		while (it.hasNext()) {
    	   int index = it.next();
    	   Solution sol = null;
    	   
    	   if (index == N_) {
    		   sol = offspring_;
    	   } else {
    		   sol = solutionSet_.get(index);
    	   }
    		   
    	   if (sol.getCrowdingDistance() < minDis ) { // 
    		   minDis = sol.getCrowdingDistance();
    		   minIdx = index;
    	   }		 
		}// while 
		
		if (minIdx == -1) {
			minIdx = subFronts_[frontID].get(PseudoRandom.randInt(0,subFronts_[frontID].size()-1));
		}
		
		it = subFronts_[frontID].iterator();	
		
		while(it.hasNext())   {  
		     if(it.next() == minIdx) {  
		         it.remove();  
		     }  
	    }
		
		if (subFronts_[frontID].size() != 0) {			
//			this.crowdingDistanceAssignment(frontID);
		} else {
			frontNumber_ --;
		}
		
		updateFWhenDelete(minIdx);
		updateMatrixWhenDelete(minIdx);
	}
	
	public void updateWhenDelete (){
		
		if (frontNumber_ == 1) {
			this.updateFrontsWhenDelete(0); // the first front
		} else {			
			this.updateFrontsWhenDelete(frontNumber_-1); // the last front 			
		}
	}
	
/**
 * The fitness assignment of each solution
 * @param type, flag = true, return solutions in each front, or return index of solutions
 * @return
 */
	public void dominanceDegreeFitness ( ){	
		int maxLevel = -1;
		/**
		 * Method 1
		 */
		for (int i=0; i< N_  + 1; i++ ) {
			int counter1 = 0;
			int counter2 = 0;
			int sum = 0;
			
			for(int j=0; j< N_ + 1;j++) {
				if (j!=i && domDegreeMat_[j][i] == M_) {
					counter1 ++;
				}
			}// for j	
			
			int dc = counter1;			
			
			fitness_ [i] = dc ;
			
			solutionSet_.get(i).setFitness(fitness_ [i]);
			
			if (dc > maxLevel) {
				maxLevel = dc;
			}
		}// for i
		 
		frontNumber_ = maxLevel + 1;
	    subFronts_ = new List[frontNumber_];
		
		 // Initialize the fronts 
	    for (int i = 0; i < subFronts_.length; i++)
	    	subFronts_[i] = new LinkedList<Integer>();    
	    
	    
		for (int k = 0; k < N_; k ++) {
			subFronts_[(int)fitness_ [k]].add(k);
		}
		
//		
//		int frontNumber = 0;
//		for (int k = 0; k < subFronts.length;k ++) {
//			if (subFronts[k].size() > 0) {
//				frontNumber ++;
//			}
//		}
//		
///**
// * Return index of solutions in each front		
// */  
//		subFronts_ = new List [frontNumber];
//		
//		int frontIdx = 0;
//		
//	    for (int j = 0; j < subFronts.length; j++) {	    	
//	       if (subFronts[j].size()!=0) {
//	    	  subFronts_[frontIdx] = new  LinkedList<Integer>();	      
//	    	  Iterator<Integer> it1 = subFronts[j].iterator();
//	 	      while (it1.hasNext()) {
//	 	    	   int solIdx = it1.next();
//	 	    	   Solution sol = solutionSet_.get(solIdx);
//	 	    	   sol.setRank(frontIdx);
//	 	    	   subFronts_[frontIdx].add(solIdx);	           
//	 	      }
//	 	     frontIdx ++;
//	       }	      
//	    }//for j

	} // dominanceDegreeFitness
	
	/**
	 * Crowding distance assignment to each front 
	 */
	public SolutionSet crowdingDistanceAssignment (int FrontID, int numberToRemove) {
		
		SolutionSet front = this.getSubfront(FrontID);
		
		int number = front.size(); // the number of members in the FrontID-th front
			
		int [] index = new int [number]; 
	
		double [][] F = new double [M_][number]; // 
		double [][] A = new double [M_][number]; // 
		int [][] B = new int [M_][number];
		int [][] C = new int [M_][number];
		double [][] D = new double [M_][number];
		double [] cd = new double [number];
		
		for (int k =0; k < number; k++) {	
			index[k] = k;
		}
        
		for (int i = 0; i < M_ ; i++) { // for each objective
		
			int [] idxAfterSorting = new int [number];
			System.arraycopy(index, 0, idxAfterSorting, 0, number);
			//F[i] 
			for (int j = 0; j < number;j++){				
				F[i][j] = front.get(j).getObjective(i);
			}
			//A[i]
			System.arraycopy(F[i], 0, A[i], 0, number);
			
			//B[i]
			Utils.QuickSort(A[i], idxAfterSorting, 0, number - 1);	
			System.arraycopy(idxAfterSorting, 0, B[i], 0, number);
						
			//C[i]
			for (int j = 0; j < number; j++) {
				C[i][B[i][j]] = j;
			}
			
			//D[i]
			
			for (int j = 0; j < number; j++) {
				if (C[i][j] == 0 ||C[i][j] == number - 1) {
					D[i][j] = Double.POSITIVE_INFINITY;					
				} else {				
					D[i][j] = Math.min(A[i][C[i][j]+ 1] - A[i][C[i][j]], A[i][C[i][j]] - A[i][C[i][j]-1])  
							/ (A[i][number-1] - A[i] [0]) + (A[i][C[i][j]+ 1] - A[i][C[i][j] - 1]) 
							/ (A[i][number - 1] - A[i] [0]) ;
				}
			}// for j	
			
		} // for m
		
		/**
		 * 	Construct cd vector
		 */
		for (int j = 0; j < number; j++) {
			// product
			cd[j] = 1.0;			
			for (int m = 0; m < M_; m++) {
				if (D[m][j] == Double.POSITIVE_INFINITY) {
					cd[j] = Double.POSITIVE_INFINITY;
					break;
				} else {
					cd[j] = cd[j] * D[m][j];
				}
			}
			front.get(j).setCrowdingDistance(cd[j]);
		}
		
		 /**
		  * Update F,A,B,C,D
		  */
		
		for (int n = 0;n < numberToRemove; n++ ) {	
			
			int k = minFastSort(cd,number); // the index in F to be deleted	
			
			// delete the kth element in cd
			deleteElemet(cd, k, number);
			
			// delete the kth element in  solutionSet
			front.remove(k);
			
			for (int i = 0;i < M_; i++) {
				
				int ck = C[i][k];// the index in A[i] to be deleted	
				
				// Update F and A			
				deleteElemet(F[i], k, number);			
				deleteElemet(A[i], ck, number);				
				double rang = A[i][number - 2] - A[i][0];		
				
				// Update c1 
				
				int [] c1 = new int[number];				
				
				// calculate c1
				for (int j = 0; j < number; j++) {
					if (j <= ck) {
						c1[B[i][j]] = C[i][B[i][j]];
					} else {
						c1[B[i][j]] = C[i][B[i][j]] - 1;
					}
				}
				
				 // Update b1				
				int [] b1 = new int[number];
				
				for (int j=0; j < number; j++) {
					if (j <= k) {
						b1[C[i][j]] = B[i][C[i][j]];
					} else {
						b1[C[i][j]] = B[i][C[i][j]] - 1;
					}
				}
				

				/**
				 * Delete  the kth element in c1 and the c(k)th element in b1 respectively
				 */	
				
				deleteElemet(c1, k, number);				
				deleteElemet(b1, ck, number);
				System.arraycopy(c1, 0, C[i], 0, number - 1);
				System.arraycopy(b1, 0, B[i], 0, number - 1);			
				
				/**
				 * Update D and cd
				 */
				
				deleteElemet(D[i], k, number);	
				
				// Update the b[c(k)-1] and b[c(k)] in D[i]	
				
				int idx1 = 0,idx2 = 0;		
				double d1 = 0.0,d2 = 0.0;				
				/**
				 * ///////////////////////////The original codes//////////////////////
				 */
				if (ck==0 || ck == number - 1) {
					if (ck == 0) {
						idx2 = B[i][ck];	
						idx1 = -1;
						d2 = D[i][idx2];
						 D[i][idx2] = Double.POSITIVE_INFINITY;
					}
					
					if (ck == number - 1) { 
						idx1 = B[i][ck-1];
						idx2 = -1;
						d1 = D[i][idx1];
						D[i][idx1] = Double.POSITIVE_INFINITY;
					}
				} else {
					
					idx1 = B[i][ck-1];
					if (C[i][idx1] == 0 ||C[i][idx1] == number - 2) {
						d1 = D[i][idx1];
						D[i][idx1] = Double.POSITIVE_INFINITY;
					} else {
						d1 = D[i][idx1];
						D[i][idx1] = Math.min(A[i][C[i][idx1]+ 1] - A[i][C[i][idx1]], A[i][C[i][idx1]] - A[i][C[i][idx1]-1]) /rang
								+ (A[i][C[i][idx1]+ 1] - A[i][C[i][idx1] - 1]) /rang;	
					}	
					
					idx2 = B[i][ck];				
					
					if (C[i][idx2] == 0 ||C[i][idx2] == number - 2) {
						d2 = D[i][idx2];
						D[i][idx2] = Double.POSITIVE_INFINITY;
					} else {
						d2 = D[i][idx2];
						D[i][idx2] = Math.min(A[i][C[i][idx2]+ 1] - A[i][C[i][idx2]], A[i][C[i][idx2]] - A[i][C[i][idx2]-1]) /rang
								+ (A[i][C[i][idx2]+ 1] - A[i][C[i][idx2] - 1]) /rang;
					}			
				}
				
				// Update cd
				
				if (idx1 != -1) {
					if (d1 != 0.0 && d1 != Double.POSITIVE_INFINITY) {
						cd[idx1] = cd[idx1]/d1 * D[i][idx1]; 
					} else {
						cd[idx1] = d1;
					}
					
					front.get(idx1).setCrowdingDistance(cd[idx1]);
				} // if dix1
			
				
				if (idx2 != -1) {
					if (d2 != 0.0 && d2 != Double.POSITIVE_INFINITY) {
						cd[idx2] = cd[idx2]/d2 * D[i][idx2]; 
					} else {
						cd[idx2] = d2;
					}
					
					front.get(idx2).setCrowdingDistance(cd[idx2]);
				} // if dix2				
								
				/**
				 * update cd use binary search
				 */	
				
			} // for i			
			number --;		
		}// for n
		return front;
	} //crowdingDistanceAssignment
	
	
	public SolutionSet execute(Solution solution) {		  
		offspring_ = solution;
		updateFWhenAdd(solution);
		
		if (!updateMatrixWhenAdd()){
			return solutionSet_;
		}
		
		updateFrontsWhenAdd();
		
	    updateWhenDelete();
//	    System.out.println("here");
		return solutionSet_;
	}
	
	
	/**
	 * Select some members according to fitness values
	 * @return
	 */
	public SolutionSet selectMembers (int numbers) {
		SolutionSet selected = new SolutionSet(numbers);
		
		double [] fit = new double [N_];
		int [] idx = new int [N_];
		
		for  (int k = 0; k < N_; k++) {
			idx[k] = k;
		}
		
		System.arraycopy(fitness_, 0, fit , 0, N_);
		 
		QSort qSort = new QSort();
		
		qSort.quicksort(fit, idx, 0, N_-1);			
			
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
