//  SolutionSet.Java
//
//  Author:
//       Antonio J. Nebro <antonio@lcc.uma.es>
//       Juan J. Durillo <durillo@lcc.uma.es>
//
//  Copyright (c) 2011 Antonio J. Nebro, Juan J. Durillo
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

package jmetal.core;

import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;

import jmetal.util.Configuration;
import jmetal.util.PseudoRandom;

/** 
 * Class representing a SolutionSet (a set of solutions)
 */
public class SolutionSet implements Serializable {

  /**
   * Stores a list of <code>solution</code> objects.
   */
  protected final List<Solution> solutionsList_;

  /** 
   * Maximum size of the solution set 
   */
//  private int capacity_ = 0; 

  private int capacity_ = Integer.MAX_VALUE;
  /**
   * Constructor.
   * Creates an unbounded solution set.
   */
  public SolutionSet() {
    solutionsList_ = new ArrayList<Solution>();
  } // SolutionSet

  /** 
   * Creates a empty solutionSet with a maximum capacity.
   * @param maximumSize Maximum size.
   */
  public SolutionSet(int maximumSize){    
    solutionsList_ = new ArrayList<Solution>();
    capacity_      = maximumSize;
  } // SolutionSet

  /** 
   * Inserts a new solution into the SolutionSet. 
   * @param solution The <code>Solution</code> to store
   * @return True If the <code>Solution</code> has been inserted, false 
   * otherwise. 
   */
  public boolean add(Solution solution) {
    if (solutionsList_.size() == capacity_) {
      Configuration.logger_.severe("The population is full");
      Configuration.logger_.severe("Capacity is : "+capacity_);
      Configuration.logger_.severe("\t Size is: "+ this.size());
      return false;
    } // if

    solutionsList_.add(solution);
    return true;
  } // add
  
  public boolean add(int index, Solution solution) {
	    solutionsList_.add(index, solution) ;
	    return true ;
	  }
  /*
  public void add(Solution solution) {
    if (solutionsList_.size() == capacity_)
      try {
        throw new JMException("SolutionSet.Add(): the population is full") ;
      } catch (JMException e) {
        e.printStackTrace();
      }
    else
      solutionsList_.add(solution);
  }
  */
  /**
   * Returns the ith solution in the set.
   * @param i Position of the solution to obtain.
   * @return The <code>Solution</code> at the position i.
   * @throws IndexOutOfBoundsException Exception
   */
  public Solution get(int i) {
    if (i >= solutionsList_.size()) {
      throw new IndexOutOfBoundsException("Index out of Bound "+i);
    }
    return solutionsList_.get(i);
  } // get

  /**
   * Returns the maximum capacity of the solution set
   * @return The maximum capacity of the solution set
   */
  public int getMaxSize(){
    return capacity_ ;
  } // getMaxSize

  /** 
   * Sorts a SolutionSet using a <code>Comparator</code>.
   * @param comparator <code>Comparator</code> used to sort.
   */
  public void sort(Comparator comparator){
    if (comparator == null) {
      Configuration.logger_.severe("No criterium for comparing exist");
      return ;
    } // if
    Collections.sort(solutionsList_,comparator);   
  } // sort

  /** 
   * Sorts a SolutionSet using a <code>Comparator</code>.
   * @param comparator <code>Comparator</code> used to sort.
   */
  public void sort(Comparator comparator,int m){
    if (comparator == null) {
      Configuration.logger_.severe("No criterium for comparing exist");
      return ;
    } // if
    int n = solutionsList_.size();
    
    for (int i = 0; i < m; i++) {
		for (int j = i + 1; j < n; j++) {
			int flag = comparator.compare(solutionsList_.get(i), solutionsList_.get(j));
			if (flag == 1) {
				Solution temp = solutionsList_.get(i);
				replace(i, solutionsList_.get(j));				
				replace(j, temp);	
			} // if
		}
	} // for

  } // sort
  /** 
   * Returns the index of the best Solution using a <code>Comparator</code>.
   * If there are more than one occurrences, only the index of the first one is returned
   * @param comparator <code>Comparator</code> used to compare solutions.
   * @return The index of the best Solution attending to the comparator or 
   * <code>-1<code> if the SolutionSet is empty
   */
   int indexBest(Comparator comparator){
    if ((solutionsList_ == null) || (this.solutionsList_.isEmpty())) {
      return -1;
    }

    int index = 0; 
    Solution bestKnown = solutionsList_.get(0), candidateSolution;
    int flag;
    for (int i = 1; i < solutionsList_.size(); i++) {        
      candidateSolution = solutionsList_.get(i);
      flag = comparator.compare(bestKnown, candidateSolution);
//      if (flag == -1) {
      if (flag == 1) {
        index = i;
        bestKnown = candidateSolution; 
      }
    }

    return index;
  } // indexBest


  /** 
   * Returns the best Solution using a <code>Comparator</code>.
   * If there are more than one occurrences, only the first one is returned
   * @param comparator <code>Comparator</code> used to compare solutions.
   * @return The best Solution attending to the comparator or <code>null<code>
   * if the SolutionSet is empty
   */
  public Solution best(Comparator comparator){
	  /**
	   * method1: the selected elite always has the infinite distance 
	   */
//    int indexBest = indexBest(comparator);
//    if (indexBest < 0) {
//      return null;
//    } else {
//      return solutionsList_.get(indexBest);
//    }

	  /**
	   * method2: the selected elite doesn't equal to the solution with infinite distance 
	   */
	  if(solutionsList_.size() ==  0){
		  return null;
	  }
	  
	  this.sort(comparator);// in ascending order, 
	  
	  if(solutionsList_.size() ==  1){
		  return solutionsList_.get(0);
	  }
	  if(solutionsList_.size() ==  2){
		  return solutionsList_.get(0);
	  }
	  	 
	  int i = 0;
	  
	  while ( Double.isInfinite(solutionsList_.get(i).getCrowdingDistance())) {		
		  i++;
	  }
	  	  
	  if (i >= 1) { // �м��˵�
		  if (PseudoRandom.randDouble() < 1.0) {
			  return solutionsList_.get(i);// the least crowded elite
		  } else {
			  return solutionsList_.get(PseudoRandom.randInt(0,i-1));
		  }
	  } else {
		  return solutionsList_.get(0);
	  }
	  
//	  return solutionsList_.get(2);
//	  return solutionsList_.get(solutionsList_.size()-1);// the most crowded elite
	  
	  /**
	   * method3: the randomly selected elite 
	   */
//	  int randomIndex = PseudoRandom.randInt(0, solutionsList_.size()-1);
//	  return solutionsList_.get(randomIndex);
	  
  } // best  


  /** 
   * Returns the index of the worst Solution using a <code>Comparator</code>.
   * If there are more than one occurrences, only the index of the first one is returned
   * @param comparator <code>Comparator</code> used to compare solutions.
   * @return The index of the worst Solution attending to the comparator or 
   * <code>-1<code> if the SolutionSet is empty
   */
  public int indexWorst(Comparator comparator){


    if ((solutionsList_ == null) || (this.solutionsList_.isEmpty())) {
      return -1;
    }

    int index = 0;
    Solution worstKnown = solutionsList_.get(0), candidateSolution;
    int flag;
    for (int i = 1; i < solutionsList_.size(); i++) {        
      candidateSolution = solutionsList_.get(i);
      flag = comparator.compare(worstKnown, candidateSolution);
//      if (flag == -1) {
      if (flag == -1) {
        index = i;
        worstKnown = candidateSolution;
      }
    }

    return index;

  } // indexWorst

  /** 
   * Returns the worst Solution using a <code>Comparator</code>.
   * If there are more than one occurrences, only the first one is returned
   * @param comparator <code>Comparator</code> used to compare solutions.
   * @return The worst Solution attending to the comparator or <code>null<code>
   * if the SolutionSet is empty
   */
  public Solution worst(Comparator comparator){

    int index = indexWorst(comparator);
    if (index < 0) {
      return null;
    } else {
      return solutionsList_.get(index);
    }

  } // worst


  /** 
   * Returns the number of solutions in the SolutionSet.
   * @return The size of the SolutionSet.
   */  
  public int size(){
    return solutionsList_.size();
  } // size

  /** 
   * Writes the objective function values of the <code>Solution</code> 
   * objects into the set in a file.
   * @param path The output file name
   */
  public void printObjectivesToFile(String path){
    try {
      /* Open the file */
      FileOutputStream fos   = new FileOutputStream(path)     ;
      OutputStreamWriter osw = new OutputStreamWriter(fos)    ;
      BufferedWriter bw      = new BufferedWriter(osw)        ;

      for (Solution aSolutionsList_ : solutionsList_) {
        //if (this.vector[i].getFitness()<1.0) {
        bw.write(aSolutionsList_.toString());
        bw.newLine();
        //}
      }

      /* Close the file */
      bw.close();
    }catch (IOException e) {
      Configuration.logger_.severe("Error acceding to the file");
      e.printStackTrace();
    }
  } // printObjectivesToFile

  /**
   * Writes the decision encodings.variable values of the <code>Solution</code>
   * solutions objects into the set in a file.
   * @param path The output file name
   */
  public void printVariablesToFile(String path){
    try {
      FileOutputStream fos   = new FileOutputStream(path)     ;
      OutputStreamWriter osw = new OutputStreamWriter(fos)    ;
      BufferedWriter bw      = new BufferedWriter(osw)        ;            

      if (size()>0) {
        int numberOfVariables = solutionsList_.get(0).getDecisionVariables().length ;
        for (Solution aSolutionsList_ : solutionsList_) {
          for (int j = 0; j < numberOfVariables; j++)
            bw.write(aSolutionsList_.getDecisionVariables()[j].toString() + " ");
          bw.newLine();
        }
      }
      bw.close();
    }catch (IOException e) {
      Configuration.logger_.severe("Error acceding to the file");
      e.printStackTrace();
    }       
  } // printVariablesToFile


  /**
   * Write the function values of feasible solutions into a file
   * @param path File name
   */
  public void printFeasibleFUN(String path) {
    try {
      FileOutputStream fos   = new FileOutputStream(path)     ;
      OutputStreamWriter osw = new OutputStreamWriter(fos)    ;
      BufferedWriter bw      = new BufferedWriter(osw)        ;

      for (Solution aSolutionsList_ : solutionsList_) {
        if (aSolutionsList_.getOverallConstraintViolation() == 0.0) {
          bw.write(aSolutionsList_.toString());
          bw.newLine();
        }
      }
      bw.close();
    }catch (IOException e) {
      Configuration.logger_.severe("Error acceding to the file");
      e.printStackTrace();
    }
  }

  
  /**
   * Write the function values of feasible solutions into a file
   * @param path File name
   */
  public void printFeasibleNormalizedFUN(String path) {
    try {
      FileOutputStream fos   = new FileOutputStream(path)     ;
      OutputStreamWriter osw = new OutputStreamWriter(fos)    ;
      BufferedWriter bw      = new BufferedWriter(osw)        ;

      for (Solution aSolutionsList_ : solutionsList_) {
        if (aSolutionsList_.getOverallConstraintViolation() == 0.0) {
          bw.write(aSolutionsList_.toStringNormalized());
          bw.newLine();
        }
      }
      bw.close();
    }catch (IOException e) {
      Configuration.logger_.severe("Error acceding to the file");
      e.printStackTrace();
    }
  }
  
  /**
   * Write the encodings.variable values of feasible solutions into a file
   * @param path File name
   */
  public void printFeasibleVAR(String path) {
    try {
      FileOutputStream fos   = new FileOutputStream(path)     ;
      OutputStreamWriter osw = new OutputStreamWriter(fos)    ;
      BufferedWriter bw      = new BufferedWriter(osw)        ;            

      if (size()>0) {
        int numberOfVariables = solutionsList_.get(0).getDecisionVariables().length ;
        for (Solution aSolutionsList_ : solutionsList_) {
          if (aSolutionsList_.getOverallConstraintViolation() == 0.0) {
            for (int j = 0; j < numberOfVariables; j++)
              bw.write(aSolutionsList_.getDecisionVariables()[j].toString() + " ");
            bw.newLine();
          }
        }
      }
      bw.close();
    }catch (IOException e) {
      Configuration.logger_.severe("Error acceding to the file");
      e.printStackTrace();
    }       
  }
  
  /** 
   * Empties the SolutionSet
   */
  public void clear(){
    solutionsList_.clear();
  } // clear

  /** 
   * Deletes the <code>Solution</code> at position i in the set.
   * @param i The position of the solution to remove.
   */
  public void remove(int i){        
    if (i > solutionsList_.size()-1) {            
      Configuration.logger_.severe("Size is: "+this.size());
    } // if
    solutionsList_.remove(i);    
  } // remove


  /**
   * Returns an <code>Iterator</code> to access to the solution set list.
   * @return the <code>Iterator</code>.
   */    
  public Iterator<Solution> iterator(){
    return solutionsList_.iterator();
  } // iterator   

  /** 
   * Returns a new <code>SolutionSet</code> which is the result of the union
   * between the current solution set and the one passed as a parameter.
   * @param solutionSet SolutionSet to join with the current solutionSet.
   * @return The result of the union operation.
   */
  public SolutionSet union(SolutionSet solutionSet) {       
    //Check the correct size. In development
    int newSize = this.size() + solutionSet.size();
    if (newSize < capacity_)
      newSize = capacity_;

    //Create a new population 
    SolutionSet union = new SolutionSet(newSize);                
    for (int i = 0; i < this.size(); i++) {      
      union.add(this.get(i));
    } // for

    for (int i = this.size(); i < (this.size() + solutionSet.size()); i++) {
      union.add(solutionSet.get(i-this.size()));
    } // for

    return union;        
  } // union                   

  /** 
   * Replaces a solution by a new one
   * @param position The position of the solution to replace
   * @param solution The new solution
   */
  public void replace(int position, Solution solution) {
    if (position > this.solutionsList_.size()) {
      solutionsList_.add(solution);
    } // if 
    solutionsList_.remove(position);
    solutionsList_.add(position,solution);
  } // replace

  /**
   * Copies the objectives of the solution set to a matrix
   * @return A matrix containing the objectives
   */
  public double [][] writeObjectivesToMatrix() {
    if (this.size() == 0) {
      return null;
    }
    double [][] objectives;
    objectives = new double[size()][get(0).numberOfObjectives()];
    for (int i = 0; i < size(); i++) {
      for (int j = 0; j < get(0).numberOfObjectives(); j++) {
        objectives[i][j] = get(i).getObjective(j);
      }
    }
    return objectives;
  } // writeObjectivesMatrix
  public double MaxOverallConViolation(){
      if ((solutionsList_ == null) || (this.solutionsList_.isEmpty())) {
        return -1;
      }
      Comparator temp = new Comparator() {
        @Override
        public int compare(Object o1, Object o2) {
          Solution a = (Solution) o1;
          Solution b = (Solution) o2;
          return (int)a.getOverallConstraintViolation() - (int)b.getOverallConstraintViolation();
        }
      };
      Solution worstKnown = solutionsList_.get(0), candidateSolution;
      int flag;
      for (int i = 1; i < solutionsList_.size(); i++) {
        candidateSolution = solutionsList_.get(i);
        flag = temp.compare(worstKnown, candidateSolution);
        if (flag == -1) {
          worstKnown = candidateSolution;
        }
      }

      return worstKnown.getOverallConstraintViolation();

    } // indexWorst
   public double GetFeasible_Ratio() {
	    double result = 0.0;
	    for (Solution aSolutionsList_ : solutionsList_) {
	      if (aSolutionsList_.getOverallConstraintViolation() == 0.0) {
	        result+=1;
	      }
	    }
	    return result / solutionsList_.size();
	  }
} // SolutionSet

