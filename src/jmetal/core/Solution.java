/**
 * 在进行OLEA实验时，该算法加入了一些新的属性
 * 作为原来solution类的备份
 */


package jmetal.core;

import java.io.Serializable;

import jmetal.encodings.variable.Binary;
import jmetal.encodings.variable.Real;

/**
 * Class representing a solution for a problem.
 */
public class Solution implements Serializable {  
 private int ID_; // The unique ID of a solution
	/**
	 * Stores the problem 
	 */
  private Problem problem_ ;
	
  /**
   * Stores the type of the encodings.variable
   */	
  private SolutionType type_ ; 

  /**
   * Stores the decision variables of the solution.
   */
  private Variable[] variable_ ;

  /**
   * Stores the objectives values of the solution.
   */
  private final double [] objective_ ;
  
  /**
   * Stores the normalized objectives values of the solution.
   */
  private  double [] normalizedObjective_ ;
  
  /**
   * Stores the number of objective values of the solution
   */
  private int numberOfObjectives_ ;
  /**
   * Stores the number of Constraints of the solution
   */
  private int numberOfConstraints_ ;

  /**
   * Stores the constraint values of the solution.
   */
  private final double [] constraint_ ;

  /**
   * Stores the so called fitness value. Used in some metaheuristics
   */
  private double fitness_ ;
  
  /**
   * Stores the aggresed function value, Used in some metaheuristics
   */
  private double fun_ ;


/**
   * Used in algorithm AbYSS, this field is intended to be used to know
   * when a <code>Solution</code> is marked.
   */
  private boolean marked_ ;

  /**
   * Stores the so called rank of the solution. Used in NSGA-II
   */
  private int rank_ ;

  /**
   * Stores the overall constraint violation of the solution.
   */
  private double  overallConstraintViolation_ ;

  /**
   * Stores the number of constraints violated by the solution.
   */
  private int  numberOfViolatedConstraints_ ;

  /**
   * This field is intended to be used to know the location of
   * a solution into a <code>SolutionSet</code>. Used in MOCell
   */
	private int location_ ;	
	  
	/**
	 * This field is intended to be used to know the region of a solution
	 * <code>SolutionSet</code>. Used in MST
	 */
	private int region_;
	
  /**
   * Stores the distance to his k-nearest neighbor into a 
   * <code>SolutionSet</code>. Used in SPEA2.
   */
  private double kDistance_ ; 

  /**
   * Stores the crowding distance of the the solution in a 
   * <code>SolutionSet</code>. Used in NSGA-II.
   */
  private double crowdingDistance_ ; 

  /**
   * Stores the distance between this solution and a <code>SolutionSet</code>.
   * Used in AbySS.
   */
  private double distanceToSolutionSet_ ;   
  
  /** 
   *  Stores the cluster ID and vDistance, Used in NSGAIII
   */
	private int clusterID_;
	
	private double vDistance_;
   /**
	* Stores diversity and associateDist, used in MOEADD
	*/
	private double diversity_;
	
	private double associateDist_;	
	
	private double distanceToIdealPoint_;
	private double distanceToReferencePoint_;
	/**
	 * Indicate the solution whether is normalized or not
	 */
	private boolean isNormalized_; 
	
	/** Used in PSO
	 * Stores the speed  of the solution.
	 */
//	private  double [] speed_ ;
	  
	/** Used in PSO
	 * Stores the pbest solutions.
	 */
//	private  SolutionSet pbest_ ;
	
  /**
   * Constructor.
   */
  public Solution() {        
  	problem_                      = null  ;
    marked_                       = false ;
    isNormalized_                 = false;
    overallConstraintViolation_   = 0.0   ;
    numberOfConstraints_= 0;
    numberOfViolatedConstraints_  = 0 ;      
    type_                         = null ;
    variable_                     = null ;
    objective_                    = null ;
    normalizedObjective_          = null ;
    constraint_                   = null ;
//    speed_                        = null ;
    distanceToIdealPoint_         = 0.0;
    distanceToReferencePoint_     = 0.0;
  } // Solution

  /**
   * Constructor
   * @param numberOfObjectives Number of objectives of the solution
   * 
   * This constructor is used mainly to read objective values from a file to
   * variables of a SolutionSet to apply quality indicators
   */
  public Solution(int numberOfObjectives) {
    numberOfObjectives_ = numberOfObjectives;
    numberOfConstraints_= 0;
    objective_          = new double[numberOfObjectives];
    normalizedObjective_ = new double[numberOfObjectives];
    constraint_    = new double[numberOfConstraints_];
  }
  
  /**
   * Constructor
   * @param numberOfObjectives Number of objectives of the solution
   * 
   * This constructor is used mainly to read objective values from a file to
   * variables of a SolutionSet to apply quality indicators
   */
  public Solution(int numberOfObjectives,int numberOfVariables) {
    numberOfObjectives_ = numberOfObjectives;    
    numberOfConstraints_= 0;
    objective_          = new double[numberOfObjectives];
    normalizedObjective_ = new double[numberOfObjectives];
    constraint_    = new double[numberOfConstraints_];
//    speed_         = new double[numberOfVariables];
    
    variable_ = new Variable[numberOfVariables];
    
    for (int var = 0; var < numberOfVariables; var++)
        variable_[var] = new Real(); 
    
  }
  
  /** 
   * Constructor.
   * @param problem The problem to solve
   * @throws ClassNotFoundException 
   */
  public Solution(Problem problem) throws ClassNotFoundException{
    problem_ = problem ; 
    type_ = problem.getSolutionType() ;
    numberOfObjectives_ = problem.getNumberOfObjectives() ;
    numberOfConstraints_ = problem.getNumberOfConstraints();
    objective_          = new double[numberOfObjectives_] ;
    normalizedObjective_ = new double[numberOfObjectives_];
    constraint_    = new double[numberOfConstraints_];    
    
    // Used in PSO
//    speed_         = new double[numberOfVariables()];
//    pbest_          = new SolutionSet(3);
    
    // Setting initial values
    fitness_              = 0.0 ;
    fun_                  = 0.0 ;                
    kDistance_            = 0.0 ;
    crowdingDistance_     = 0.0 ;        
    distanceToSolutionSet_ = Double.POSITIVE_INFINITY ;
    distanceToIdealPoint_  = 0.0 ;
    distanceToReferencePoint_ = 0.0;
    overallConstraintViolation_  = 0.0;
    numberOfViolatedConstraints_ = 0;
    marked_                 = false; 
    isNormalized_           = false; 
    //<-

    //variable_ = problem.solutionType_.createVariables() ; 
    variable_ = type_.createVariables() ; 
  } // Solution
  
  static public Solution getNewSolution(Problem problem) throws ClassNotFoundException {
    return new Solution(problem) ;
  }
  
  /** 
   * Constructor
   * @param problem The problem to solve
   */
  public Solution(Problem problem, Variable [] variables){
    problem_ = problem ;
  	type_ = problem.getSolutionType() ;
    numberOfObjectives_ = problem.getNumberOfObjectives() ;
    numberOfConstraints_ = problem.getNumberOfConstraints();
    objective_          = new double[numberOfObjectives_] ;
    normalizedObjective_ = new double[numberOfObjectives_];
    constraint_    = new double[numberOfConstraints_];
//    speed_         = new double[numberOfVariables()];
    
    // Setting initial values
    fitness_              = 0.0 ;
    fun_                  = 0.0 ;
    kDistance_            = 0.0 ;
    crowdingDistance_     = 0.0 ;        
    distanceToSolutionSet_ = Double.POSITIVE_INFINITY ;
    distanceToIdealPoint_  = 0.0 ;
    distanceToReferencePoint_ = 0.0;
    overallConstraintViolation_  = 0.0;
    numberOfViolatedConstraints_ = 0;
    isNormalized_           = false; 
    //<-

    variable_ = variables ;
  } // Constructor
  
  /** 
   * Copy constructor.
   * @param solution Solution to copy.
   */    
  public Solution(Solution solution) {            
    problem_ = solution.problem_ ;
    type_ = solution.type_;

    numberOfObjectives_ = solution.numberOfObjectives();
    numberOfConstraints_ = solution.getNumberOfConstraints();
    objective_ = new double[numberOfObjectives_];
    normalizedObjective_ = new double[numberOfObjectives_];
    constraint_    = new double[numberOfConstraints_];
//    speed_         = new double[numberOfVariables()];
    
    for (int i = 0; i < objective_.length;i++) {
      objective_[i] = solution.getObjective(i);
      normalizedObjective_[i] =  solution.getNormalizedObjective(i);
    } // for
    
    for (int i = 0; i < constraint_.length;i++) {
    	constraint_[i] = solution.getConstraint(i);        
      } // for
    
//    for (int var = 0; var < speed_.length; var++) {
//    	speed_[var] = solution.getSpeed(var);        
//     } // for
//     pbest_ = solution.getPbest();   
    
    variable_ = type_.copyVariables(solution.variable_) ;
    ID_            = solution.getID();     
    overallConstraintViolation_  = solution.getOverallConstraintViolation();
    numberOfViolatedConstraints_ = solution.getNumberOfViolatedConstraint();
    distanceToSolutionSet_ = solution.getDistanceToSolutionSet();
    distanceToIdealPoint_ = solution.getDistanceToIdealPoint();
    distanceToReferencePoint_ = solution.getDistanceToReferencePoint();
    crowdingDistance_     = solution.getCrowdingDistance();
    kDistance_            = solution.getKDistance();                
    fitness_              = solution.getFitness();
    fun_                  = solution.getFun();
    marked_               = solution.isMarked();
    isNormalized_         = solution.isNormalized(); 
    rank_                 = solution.getRank();
    location_             = solution.getLocation();   
    
    // Used in NSGAIII
    clusterID_  = solution.getClusterID();
    vDistance_   = solution.getVDistance();
    // Used in MOEADD
    diversity_       = solution.getDiversity();
    associateDist_ = solution.getAssociateDist();   
    region_   = solution.readRegion();
  } // Solution

  /** 
   * Copy constructor.
   * @param solution Solution to copy.
   */    
  public Solution(Solution solution, boolean copyObjOnly) {            
    numberOfObjectives_ = solution.numberOfObjectives(); 
    objective_ = new double[numberOfObjectives_];
    constraint_    = new double[numberOfConstraints_];
    
    for (int i = 0; i < objective_.length;i++) {
      objective_[i] = solution.getObjective(i); 
    } // for
   
  } // Solution
  
  /**
   * Sets the distance between this solution and a <code>SolutionSet</code>.
   * The value is stored in <code>distanceToSolutionSet_</code>.
   * @param distance The distance to a solutionSet.
   */
  public void setDistanceToSolutionSet(double distance){
    distanceToSolutionSet_ = distance;
  } // SetDistanceToSolutionSet

  /**
   * Gets the distance from the solution to a <code>SolutionSet</code>. 
   * <b> REQUIRE </b>: this method has to be invoked after calling 
   * <code>setDistanceToPopulation</code>.
   * @return the distance to a specific solutionSet.
   */
  public double getDistanceToSolutionSet(){
    return distanceToSolutionSet_;
  } // getDistanceToSolutionSet


  /** 
   * Sets the distance between the solution and its k-nearest neighbor in 
   * a <code>SolutionSet</code>. The value is stored in <code>kDistance_</code>.
   * @param distance The distance to the k-nearest neighbor.
   */
  public void setKDistance(double distance){
    kDistance_ = distance;
  } // setKDistance

  /** 
   * Gets the distance from the solution to his k-nearest nighbor in a 
   * <code>SolutionSet</code>. Returns the value stored in
   * <code>kDistance_</code>. <b> REQUIRE </b>: this method has to be invoked 
   * after calling <code>setKDistance</code>.
   * @return the distance to k-nearest neighbor.
   */
  double getKDistance(){
    return kDistance_;
  } // getKDistance

  /**
   * Sets the crowding distance of a solution in a <code>SolutionSet</code>.
   * The value is stored in <code>crowdingDistance_</code>.
   * @param distance The crowding distance of the solution.
   */  
  public void setCrowdingDistance(double distance){
    crowdingDistance_ = distance;
  } // setCrowdingDistance


  /** 
   * Gets the crowding distance of the solution into a <code>SolutionSet</code>.
   * Returns the value stored in <code>crowdingDistance_</code>.
   * <b> REQUIRE </b>: this method has to be invoked after calling 
   * <code>setCrowdingDistance</code>.
   * @return the distance crowding distance of the solution.
   */
  public double getCrowdingDistance(){
    return crowdingDistance_;
  } // getCrowdingDistance

  /**
   * Sets the fitness of a solution.
   * The value is stored in <code>fitness_</code>.
   * @param fitness The fitness of the solution.
   */
  public void setFitness(double fitness) {
    fitness_ = fitness;
  } // setFitness

  /**
   * Gets the fitness of the solution.
   * Returns the value of stored in the encodings.variable <code>fitness_</code>.
   * <b> REQUIRE </b>: This method has to be invoked after calling 
   * <code>setFitness()</code>.
   * @return the fitness.
   */
  public double getFitness() {
    return fitness_;
  } // getFitness

/**
   * Sets the value of the i-th objective.
   * @param i The number identifying the objective.
   * @param value The value to be stored.
   */
  public void setObjective(int i, double value) {
    objective_[i] = value;
  } // setObjective
  
  /**
   * Returns the value of the i-th objective.
   * @param i The value of the objective.
   */
  public double getObjective(int i) {
    return objective_[i];
  } // getObjective
  
	/**
	 * Returns an array containing the objectives of this solution. Modifying
	 * the returned array will not modify the internal state of this solution.
	 * 
	 * @return an array containing the objectives of this solution
	 */
	public double[] getObjectives() {
		return objective_.clone();
	}
	
  /**
   * Sets the value of the i-th constraint.
   * @param i The number identifying the objective.
   * @param value The value to be stored.
   */
  public void setConstraint(int i, double value) {
	  constraint_[i] = value;
  } // setConstraint
  
  /**
   * Returns the value of the i-th constraint.
   * @param i The value of the objective.
   */
  public double getConstraint(int i) {
    return constraint_[i];
  } // getConstraint
  

  
  /**
   * Sets the value of the i-th normalized objective.
   * @param i The number identifying the objective.
   * @param value The value to be stored.
   */
  public void setNormalizedObjective(int i, double value) {
	  normalizedObjective_[i] = value;
  } // setNormalizedObjective
  
  /**
   * Returns the value of the i-th normalized objective.
   * @param i The value of the objective.
   */
  public double getNormalizedObjective(int i) {
    return normalizedObjective_[i];
  } // getNormalizedObjective
  
  /**
   * Returns the value of normalized objectives.
   * @param
   */
  public double[] getNormalizedObjectives( ) {
    return normalizedObjective_;
  } // getNormalizedObjectives

  /**
   * Returns the number of objectives.
   * @return The number of objectives.
   */
  public int getNumberOfObjectives() {
    if (objective_ == null)
      return 0 ;
    else
      return numberOfObjectives_;
  } // getNumberOfObjectives
  
  /**
   * Returns the number of objectives.
   * @return The number of objectives.
   */
  public int numberOfObjectives() {
    if (objective_ == null)
      return 0 ;
    else
      return numberOfObjectives_;
  } // numberOfObjectives

  /**  
   * Returns the number of decision variables of the solution.
   * @return The number of decision variables.
   */
  public int numberOfVariables() {
    return problem_.getNumberOfVariables() ;
  } // numberOfVariables

  /** 
   * Returns a string representing the solution.
   * @return The string.
   */
  public String toString() {
    String aux="";
    for (int i = 0; i < this.numberOfObjectives_; i++)
      aux = aux + this.getObjective(i) + " ";

    return aux;
  } // toString

  /** 
   * Returns a string representing the solution.
   * @return The string.
   */
  public String toStringNormalized() {
    String aux="";
    for (int i = 0; i < this.numberOfObjectives_; i++)
      aux = aux + this.getNormalizedObjective(i) + " ";

    return aux;
  } // toString
  
  /**
   * Returns the decision variables of the solution.
   * @return the <code>DecisionVariables</code> object representing the decision
   * variables of the solution.
   */
  public Variable[] getDecisionVariables() {
    return variable_ ;
  } // getDecisionVariables

  /**
   * Sets the decision variables for the solution.
   * @param variables The <code>DecisionVariables</code> object
   * representing the decision variables of the solution.
   */
  public void setDecisionVariables(Variable [] variables) {
    variable_ = variables ;
  } // setDecisionVariables

  /**
   * Indicates if the solution is marked.
   * @return true if the method <code>marked</code> has been called and, after 
   * that, the method <code>unmarked</code> hasn't been called. False in other
   * case.
   */
  public boolean isMarked() {
    return this.marked_;
  } // isMarked

  /**
   * Establishes the solution as marked.
   */
  public void marked() {
    this.marked_ = true;
  } // marked

  /**
   * Established the solution as unmarked.
   */
  public void unMarked() {
    this.marked_ = false;
  } // unMarked

  /**  
   * Sets the rank of a solution. 
   * @param value The rank of the solution.
   */
  public void setRank(int value){
    this.rank_ = value;
  } // setRank

  /**
   * Gets the rank of the solution.
   * <b> REQUIRE </b>: This method has to be invoked after calling 
   * <code>setRank()</code>.
   * @return the rank of the solution.
   */
  public int getRank(){
    return this.rank_;
  } // getRank

  /**
   * Sets the overall constraints violated by the solution.
   * @param value The overall constraints violated by the solution.
   */
  public void setOverallConstraintViolation(double value) {
    this.overallConstraintViolation_ = value;
  } // setOverallConstraintViolation

  /**
   * Gets the overall constraint violated by the solution.
   * <b> REQUIRE </b>: This method has to be invoked after calling 
   * <code>overallConstraintViolation</code>.
   * @return the overall constraint violation by the solution.
   */
  public double getOverallConstraintViolation() {
    return this.overallConstraintViolation_;
  }  //getOverallConstraintViolation


  /**
   * Sets the number of constraints violated by the solution.
   * @param value The number of constraints violated by the solution.
   */
  public void setNumberOfViolatedConstraint(int value) {
    this.numberOfViolatedConstraints_ = value;
  } //setNumberOfViolatedConstraint

  /**
   * Gets the number of constraint violated by the solution.
   * <b> REQUIRE </b>: This method has to be invoked after calling
   * <code>setNumberOfViolatedConstraint</code>.
   * @return the number of constraints violated by the solution.
   */
  public int getNumberOfViolatedConstraint() {
    return this.numberOfViolatedConstraints_;
  } // getNumberOfViolatedConstraint

  /**
   * Sets the location of the solution into a solutionSet. 
   * @param location The location of the solution.
   */
  public void setLocation(int location) {
    this.location_ = location;
  } // setLocation

  /**
   * Gets the location of this solution in a <code>SolutionSet</code>.
   * <b> REQUIRE </b>: This method has to be invoked after calling
   * <code>setLocation</code>.
   * @return the location of the solution into a solutionSet
   */
  public int getLocation() {
    return this.location_;
  } // getLocation
  
  public int getNumberOfConstraints() {
	return numberOfConstraints_;
}

public void setNumberOfConstraints(int numberOfConstraints) {
	this.numberOfConstraints_ = numberOfConstraints;
}
  /**
   * Sets the type of the encodings.variable.
   * @param type The type of the encodings.variable.
   */
  //public void setType(String type) {
   // type_ = Class.forName("") ;
  //} // setType

/**
   * Sets the type of the encodings.variable.
   * @param type The type of the encodings.variable.
   */
  public void setType(SolutionType type) {
    type_ = type ;
  } // setType

  /**
   * Gets the type of the encodings.variable
   * @return the type of the encodings.variable
   */
  public SolutionType getType() {
    return type_;
  } // getType

  /** 
   * Returns the aggregative value of the solution
   * @return The aggregative value.
   */
  public double getAggregativeValue() {
    double value = 0.0;                
    for (int i = 0; i < numberOfObjectives(); i++){            
      value += getObjective(i);
    }                
    return value;
  } // getAggregativeValue
  
	public double getFun() {
		return fun_;
	}
	
	public void setFun(double fun_) {		
		this.fun_ = fun_;		
	}


	public int getClusterID() {
		return clusterID_;
	}
	
	public void setClusterID(int clusterID_) {
		this.clusterID_ = clusterID_;
	}
	
	public double getVDistance() {
		return vDistance_;
	}
	
	public void setVDistance(double vDistance_) {
		this.vDistance_ = vDistance_;
	}

	public double getAssociateDist() {
		return associateDist_;
	}

	public void setAssociateDist(double associateDist_) {
		this.associateDist_ = associateDist_;
	}
	public int readRegion() {
		return this.region_;
	}
	public void setRegion(int i) {
		this.region_ = i;
	}
	public void Set_associateDist(double distance) {
		this.associateDist_ = distance;
	}

	public double read_associateDist() {
		return this.associateDist_;
	}

	public double getDiversity() {
		return diversity_;
	}

	public void setDiversity(double diversity_) {
		this.diversity_ = diversity_;
	}

	public double getDistanceToIdealPoint() {
		return distanceToIdealPoint_;
	}

	public void setDistanceToIdealPoint(double distanceToIdealPoint) {
		this.distanceToIdealPoint_ = distanceToIdealPoint;
	}
		

	public double getDistanceToReferencePoint() {
		return distanceToReferencePoint_;
	}

	public void setDistanceToReferencePoint(double distanceToReferencePoint_) {
		this.distanceToReferencePoint_ = distanceToReferencePoint_;
	}

	public boolean isNormalized() {
		return isNormalized_;
	}

	public void setNormalized(boolean isNormalized) {
		this.isNormalized_ = isNormalized;
	}

	public int getID() {
		return ID_;
	}

	public void setID(int iD) {
		ID_ = iD;
	}

	public void setMarked(boolean marked_) {
		this.marked_ = marked_;
	}

	
//	public double getSpeed(int var) {
//		return speed_[var];
//	}
//
//	public void setSpeed_(int var, double speed) {
//		this.speed_[var] = speed;
//	}
//
//	public SolutionSet getPbest() {
//		return pbest_;
//	}
//
//	public void setPbest(SolutionSet pbest) {
//		this.pbest_ = pbest;
//	}
	
  
} // Solution
