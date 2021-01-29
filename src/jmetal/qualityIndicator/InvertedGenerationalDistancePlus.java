//  InvertedGenerationalDistancePlus.java
//
//  Author:
//       Yi Xiang <gzhuxiang_yi@163.com>
//

package jmetal.qualityIndicator;


/**
 * This class implements the inverted generational distance plus metric. 
 */
public class InvertedGenerationalDistancePlus {
  public jmetal.qualityIndicator.util.MetricsUtil utils_;  //utils_ is used to access to the MetricsUtil funcionalities
  
  static final double pow_ = 2.0;          //pow. This is the pow used for the distances
  
  /**
   * Constructor.
   * Creates a new instance of the generational distance metric. 
   */
  public InvertedGenerationalDistancePlus() {
    utils_ = new jmetal.qualityIndicator.util.MetricsUtil();
  } // GenerationalDistance
  
  /**
   * Returns the inverted generational distance value for a given front
   * @param front The front 
   * @param trueParetoFront The true pareto front
   */
  public double invertedGenerationalDistancePlus(double [][] front, 
		  				double [][] trueParetoFront, int numberOfObjectives) {
        
    /**
     * Stores the maximum values of true pareto front.
     */
    double [] maximumValue ;
    
    /**
     * Stores the minimum values of the true pareto front.
     */
    double [] minimumValue ;
    
    /**
     * Stores the normalized front.
     */
    double [][] normalizedFront ;
    
    /**
     * Stores the normalized true Pareto front.
     */ 
    double [][] normalizedParetoFront ; 
    
    if (front.length == 0) {
    	System.out.println("The front is empty, return Double.Max");
    	return Double.MAX_VALUE;
    }
    
    // STEP 1. Obtain the maximum and minimum values of the Pareto front
    maximumValue = utils_.getMaximumValues(trueParetoFront, numberOfObjectives);
    minimumValue = utils_.getMinimumValues(trueParetoFront, numberOfObjectives);
    
    // STEP 2. Get the normalized front and true Pareto fronts
    normalizedFront       = utils_.getNormalizedFront(front, maximumValue, minimumValue);
    normalizedParetoFront = utils_.getNormalizedFront(trueParetoFront, maximumValue,minimumValue);
    

    // No normalization
//    normalizedFront       = front;    
//    normalizedParetoFront = trueParetoFront;    
    
    // STEP 3. Sum the distances between each point of the true Pareto front and
    // the nearest point in the true Pareto front
    double sum = 0.0;
    
    for (double[] aNormalizedParetoFront : normalizedParetoFront) {
    	double d = utils_.ParetoDistanceToClosedPoint(aNormalizedParetoFront,  normalizedFront);
    	sum += d;
    }
   
    // STEP 4. Divide the sum by the maximum number of points of the front
    double generationalDistance = sum / normalizedParetoFront.length;
    
    return generationalDistance;
  } // InvertedGenerationalDistancePlus
  
} // InvertedGenerationalDistancePlus
