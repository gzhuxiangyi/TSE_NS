//  C-Metric.java
//
//  Author:
//       Yi Xiang <gzhuxiang_yi@163.com>
//

package jmetal.qualityIndicator;


/**
 * This class implements the inverted generational distance plus metric. 
 */
public class CMetric {
  public jmetal.qualityIndicator.util.MetricsUtil utils_;  //utils_ is used to access to the MetricsUtil funcionalities
  
  static final double pow_ = 2.0;          //pow. This is the pow used for the distances
  
  /**
   * Constructor.
   * Creates a new instance of the generational distance metric. 
   */
  public CMetric() {
    utils_ = new jmetal.qualityIndicator.util.MetricsUtil();
  } // GenerationalDistance
  
  /**
   * Returns the inverted generational distance value for a given front
   * @param frontA The front A
   * @param frontB The front B
   */
  public double CMetric(double [][] frontA, double [][] frontB, int numberOfObjectives) {
        
          
    // STEP 3. Sum the distances between each point of the true Pareto front and
    // the nearest point in the true Pareto front
    int count = 0;
    
    for (double[] afrontInB : frontB) {

    	for(double [] afrontInA:frontA) {  
    		if (utils_.chekDominance(afrontInA, afrontInB) == -1) { // afrontInA dominates afrontInB
    			count += 1; break;
    		}
    	}
    	
    }
   
    // STEP 4. Divide the sum by the maximum number of points of the front
    double Cm = (double)count / frontB.length;    
   
    return Cm;
  } // CMetric
  
} // CMetric
