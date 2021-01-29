//  PD.java
//
//  Author:
//      Yi Xiang (gzhuxiang_yi@163.com)
//
//  This program is free software: you can redistribute it and/or modify
//  it under the terms of the GNU Lesser General Public License as published by
//  the Free Software Foundation, either version 3 of the License, or
//  (at your option) any later version.
//
//  This program is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU Lesser General Public License for more details.
// 
//  You should have received a copy of the GNU Lesser General Public License
//  along with this program.  If not, see <http://www.gnu.org/licenses/>.

package jmetal.qualityIndicator;

/**
 * This class implements the PD metric.  
 * Reference: Wang H, Jin Y, Yao X. Diversity Assessment in Many-Objective Optimization[J]. 2016.
 */
public class PD {
  public jmetal.qualityIndicator.util.MetricsUtil utils_;  //utils_ is used to access to the
                                           //MetricsUtil funcionalities
  
  static final double pow_ = 0.1;          //pow. This is the pow used for the
                                           //distances
  private double [][] D; // the dissimilarity matrix
  /**
   * Constructor.
   * Creates a new instance of the generational distance metric. 
   */
  public PD() {
    utils_ = new jmetal.qualityIndicator.util.MetricsUtil();
  } // GenerationalDistance
  
  /**
   * Returns the PD for a given front
   * @param front The front 
   */
  public double PD(double [][] front, int numberOfObjectives) {
      int n = front.length; // n solutions
	 
	 
	  D = new double [n][n];
	  int [] min_index = new int [n];
	  double [] min_d = new double [n];
	  boolean [] removed = new boolean [n];
	  
	  double PD = 0.0;
	  
	  // Step 1: Construct D matrix 
	  for (int i = 0; i < n; i++) {
		  for (int j = 0; j < n; j++) {
			  if (i == j) {
				  D[i][j] = Double.MAX_VALUE;			
			  } else {
				  D[i][j] = L_p_distance(front[i],front[j]);				  
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
  
  /**
   * Returns the PD for a given front
   * @param front The front 
   */
  public double UD(double [][] front, int numberOfObjectives) {
      int n = front.length; // n solutions
	 
	 
	  D = new double [n][n];
	  int [] min_index = new int [n];
	  double [] min_d = new double [n];
	  boolean [] removed = new boolean [n];
	  
	  double UD = 0.0;
	  
	  // Step 1: Construct D matrix 
	  for (int i = 0; i < n; i++) {
		  for (int j = 0; j < n; j++) {
			  if (i == j) {
				  D[i][j] = Double.MAX_VALUE;			
			  } else {
				  D[i][j] = L_p_distance(front[i],front[j]);				  
			  }
		  }
	  }
	  
	  
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
	  
	  
	  double sum_d = 0.0;
	  
	  for (int i = 0; i < n ; i++) {
		  sum_d = sum_d +  min_d [i] ;
	  }
	  
	  
	  double mean_d = sum_d/n;
	  
	  
	  for (int i = 0; i < n ; i++) {
		  UD = UD +  (min_d [i] - mean_d) *  (min_d [i] - mean_d);
	  }	  
			  
	  UD = UD/(n-1);
	  
      return UD;

  } // UD
  
  /**
   * Returns the PD for a given front
   * @param front The front 
   */
  public double PD(double [][] solutionFront, int numberOfObjectives, String problem) {
	  
	  double [] lower = new double [numberOfObjectives];
	  double [] upper = new double [numberOfObjectives];
	  
	  for (int i = 0; i < numberOfObjectives; i++) {
		  lower [i] = 0.0;
		  
		  if (problem.contains("DTLZ")) {
			  
			  if (problem.equalsIgnoreCase("DTLZ1")) {
				  upper[i] = 0.5;
			  } else if (problem.equalsIgnoreCase("ScaledDTLZ1")) {
				  
				    double factor ; 
				    if (numberOfObjectives == 3)
				    	factor = 10.0;
					else if (numberOfObjectives == 5)
						factor = 10.0;
					else if (numberOfObjectives == 8)
						factor = 3.0;
					else if (numberOfObjectives == 10)
						factor = 2.0;
					else if (numberOfObjectives == 15)
						factor = 1.2;
					else if (numberOfObjectives == 20)
						factor = 1.2;
					else if (numberOfObjectives == 25)
						factor = 1.1;
					else 
						factor = 1.0;
				    
				   upper[i] = 0.5 * Math.pow(factor, i);
				   
			  } else if (problem.equalsIgnoreCase("ScaledDTLZ2")) {
				  
				    double factor ; 				
    				if (numberOfObjectives == 3)
    					factor = 10.0;
    				else if (numberOfObjectives == 5)
    					factor = 10.0;
    				else if (numberOfObjectives == 8)
    					factor = 3.0;
    				else if (numberOfObjectives == 10)
    					factor = 3.0;
    				else if (numberOfObjectives == 15)
    					factor = 2.0;
    				else if (numberOfObjectives == 20)
    					factor = 1.2;
    				else if (numberOfObjectives == 25)
    					factor = 1.1;
    				else 
    					factor = 1.0;
				    
				   upper[i] = 1.0 * Math.pow(factor, i);
			  } else if (problem.equalsIgnoreCase("DTLZ7")) {
//				  lower [i] = Double.MIN_VALUE;
				  upper[i] = 2 * numberOfObjectives;
			  } else {
				  upper[i] = 1.0;				 
			  }
			  
		  } else if (problem.contains("WFG")) {
			  
			  upper[i] = 2.0 * (i+1);
			  
		  } else {
			  System.out.println("Upper bounder undifined!!!!!!!!!!!!!!!!");// if 
		  }
		 
	  } // for 
	  
	  boolean [] discarded = new boolean [solutionFront.length] ;
	  int noOfRemoved = 0;
	  
	  for (int i = 0; i < solutionFront.length; i++) {
		  
		  for (int j = 0 ; j < numberOfObjectives; j ++) {
			  
			  if (solutionFront[i][j] > 1.00 * upper[j] || solutionFront[i][j] < lower[j]) {
				  discarded[i] = true;
				  noOfRemoved ++;
				  break;
			  }
			  
		  } // for j
		  
	  } // for i
	  
	  System.out.println("noOfRemoved = " + noOfRemoved);
	  
	  double [][] front = new double [solutionFront.length - noOfRemoved][numberOfObjectives];
	  
      int n = front.length; // n solutions
	 
      int m = 0;
      
      for (int i = 0; i < solutionFront.length; i++) {
	      
    	  if (discarded[i] == false) {
    		  
    		  for (int j = 0; j < numberOfObjectives;j ++) {
    			  front [m][j] = (solutionFront[i][j] - lower[j])/(upper[j] - lower[j]);
    		  }
    		  
    		  m++;
    		  
    	  } // if 
	      
      } // for i
      
	 
	  D = new double [n][n];
	  int [] min_index = new int [n];
	  double [] min_d = new double [n];
	  boolean [] removed = new boolean [n];
	  
	  double PD = 0.0;
	  
	  // Step 1: Construct D matrix 
	  for (int i = 0; i < n; i++) {
		  for (int j = 0; j < n; j++) {
			  if (i == j) {
				  D[i][j] = Double.MAX_VALUE;			
			  } else {
				  D[i][j] = L_p_distance(front[i],front[j]);				  
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
  
  /**
   * Returns the PD for a given front
   * @param front The front 
   */
  public double PD(double [][] solutionFront, double [][] trueFront, int numberOfObjectives) {
	  
	  double [] lower = new double [numberOfObjectives];
	  double [] upper = new double [numberOfObjectives];
	  
	  double []   maximumValue = utils_.getMaximumValues(trueFront, numberOfObjectives);
	  double []   minimumValue = utils_.getMinimumValues(trueFront, numberOfObjectives);
	    
	  for (int i = 0; i < numberOfObjectives; i++) {
		  lower [i] = minimumValue[i];				  
		  upper[i] = maximumValue[i];		 
	  } // for 
	  
	  boolean [] discarded = new boolean [solutionFront.length] ;
	  int noOfRemoved = 0;
	  
	  for (int i = 0; i < solutionFront.length; i++) {
		  
		  for (int j = 0 ; j < numberOfObjectives; j ++) {
			  
			  if (solutionFront[i][j] > 1.00 * upper[j] || solutionFront[i][j] < lower[j]) {
				  discarded[i] = true;
				  noOfRemoved ++;
				  break;
			  }
			  
		  } // for j
		  
	  } // for i
	  
	  System.out.println("noOfRemoved = " + noOfRemoved);
	  
	  double [][] front = new double [solutionFront.length - noOfRemoved][numberOfObjectives];
	  
      int n = front.length; // n solutions
	 
      int m = 0;
      
      for (int i = 0; i < solutionFront.length; i++) {
	      
    	  if (discarded[i] == false) {
    		  
    		  for (int j = 0; j < numberOfObjectives;j ++) {
    			  front [m][j] = (solutionFront[i][j] - lower[j])/(upper[j] - lower[j]);
    		  }
    		  
    		  m++;
    		  
    	  } // if 
	      
      } // for i
      
	 
	  D = new double [n][n];
	  int [] min_index = new int [n];
	  double [] min_d = new double [n];
	  boolean [] removed = new boolean [n];
	  
	  double PD = 0.0;
	  
	  // Step 1: Construct D matrix 
	  for (int i = 0; i < n; i++) {
		  for (int j = 0; j < n; j++) {
			  if (i == j) {
				  D[i][j] = Double.MAX_VALUE;			
			  } else {
				  D[i][j] = L_p_distance(front[i],front[j]);				  
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
  
  /**
   * Return the l_p distance between two vectors a and b
   * @param a
   * @param b
   * @return
   */
  public double L_p_distance(double [] a, double [] b) {
	  double l_p_dis = 0.0;
	  int obj = a.length; 
	  
	  for (int i = 0; i < obj; i++) {
		  l_p_dis = l_p_dis + Math.pow(Math.abs(a[i] - b[i]), pow_);
	  }
	  
	  l_p_dis = Math.pow(l_p_dis, 1.0/pow_);
			  
	  return l_p_dis;
  }
  
  /**
   * This class can be invoqued from the command line. Two params are required:
   * 1) the name of the file containing the front, and 2) the name of the file 
   * containig the true Pareto front
   **/
  public static void main(String[] args) {       
    String path = "./paretoFronts/DTLZ&WFG/DTLZ13.pf";
    // STEP 1. Create an instance of Generational Distance
    PD qualityIndicator = new PD();
    
    // STEP 2. Read the fronts from the files
    double [][] trueFront     = qualityIndicator.utils_.readFront(path);
    
    // STEP 3. Obtain the metric value
    double value = qualityIndicator.PD( trueFront, 3);
    
    System.out.println(value);  
  } // main  
  
} // PD
