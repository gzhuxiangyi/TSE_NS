 /* 
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
 * 
 */
package spl;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import javax.management.JMException;

import jmetal.encodings.variable.Binary;
import spl.utils.PseudoRandom;



public class ProbSATLocalSearch  {

	private static final long serialVersionUID = 1L;
//	long SATtimeout_ = 1000 * 20;
	/**
     * Stores the problem to solve
     */ 
    
    List<Integer> featureIndicesAllowedFlip_;
    List<List<Integer>> constraints_;
    List<List<Integer>> var_poslit_;     
    List<List<Integer>> var_neglit_; 
    int []   sat_count_;	// ÿ���Ӿ������ָ���    
    Binary bin_ ; 
    double wp_;
    int unsat_stack_fill_pointer ;
    int	[]	index_in_unsat_stack;//which position is a clause in the unsat_stack
    int	[]	unsat_stack;		//store the unsat clause number
    
    
    int step_;    
    int max_flips_;
    int num_clauses_; // �־����
    int num_vars_; // ����ı�ı�������
    int unsat_stack_fill_pointer_;
    List<Integer> unsat_;
    
    public ProbSATLocalSearch(HashMap<String, Object> parameters) {
      	      			
      	if (parameters.get("max_flips") != null)
      		max_flips_ = (Integer) parameters.get("max_flips") ;     
//      	if (parameters.get("SATtimeout") != null)
//      		SATtimeout_ = (Long) parameters.get("SATtimeout") ;   
      	if (parameters.get("wp") != null)
      		wp_ = (Double) parameters.get("wp") ;  	
    
      	step_          = 0      ;
      	unsat_stack_fill_pointer_ = 0;
      	
//      	featureIndicesAllowedFlip_ = LSSATVaEA_Problem.getFeatureIndicesAllowedFlip();
      	constraints_               = (List<List<Integer>>) parameters.get("constraints");
        
      	num_clauses_               = constraints_.size();
      	num_vars_                  = (Integer) parameters.get("num_vars");; // featureIndicesAllowedFlip_.size();
      	
      	sat_count_                 = new int[num_clauses_];
      	
      	var_poslit_                = new ArrayList<List<Integer>>(num_vars_);
      	var_neglit_                = new ArrayList<List<Integer>>(num_vars_);
      	index_in_unsat_stack       = new int [num_clauses_];
      	unsat_stack                = new int [num_clauses_];
      	
      	//Initialize arrays
      	int [] var_poslit_count = new int[num_vars_];
      	int [] var_neglit_count = new int[num_vars_];
      	
      	for (int c = 0; c < num_clauses_; c++) {
      		for (int i = 0 ; i < constraints_.get(c).size();i++) {
      			int lit = constraints_.get(c).get(i);
      			int var = Math.abs(lit) - 1; // constraint�е������±��1  
      			if (lit > 0) {
      				var_poslit_count[var]++;
      			} else {
      				var_neglit_count[var]++;
      			}
      				
      		} // for i
      		
         } // for c      	
      	
      //create var literal arrays
    	for (int v=0; v < num_vars_; ++v)    	{
    		var_poslit_.add(v, new ArrayList<Integer>(var_poslit_count[v])); 
    		var_neglit_.add(v, new ArrayList<Integer>(var_neglit_count[v]));
    	}
      	
    	//Scan all clauses to build up var literal arrays
    	for (int c = 0; c < num_clauses_; ++c) 
    	{
    		for(int i = 0; i < constraints_.get(c).size(); ++i)
    		{
    			int lit = constraints_.get(c).get(i);
      			int var = Math.abs(lit) - 1; // constraint�е������±��1   	
      			
    			if(lit > 0) {
    				var_poslit_.get(var).add(c);    				
    			}
    			else  {
    				var_neglit_.get(var).add(c);    
    			}
    		}
    	}	
    	
      } //WalkSATLocalSearch 
    
  		 
	  /** 
	   * Returns the number of evaluations made
	   */    
	  public int getEvaluations() {
	    return step_;
	  } // evaluations
	
	public Object execute(Object object) throws JMException {
		
		 bin_ = (Binary) object;
//		 printVar();
		
		 init();
		 
		 if (unsat_stack_fill_pointer == 0) return bin_;	
		 
		 localSearch() ;
		 
		 if (unsat_stack_fill_pointer == 0) return bin_;	 
		 
		return bin_;
	}

	//initiation of the algorithm
	public void init()	{
		int 		c;
		int			j;
		
		unsat_stack_fill_pointer = 0;
		
		/* figure out sat_count, and init unsat_stack */			
		for (c = 0; c < num_clauses_; ++c) 	{
			sat_count_[c] = 0;
			
			for(j = 0; j < constraints_.get(c).size(); ++j) {
				int lit = constraints_.get(c).get(j);
				int var = Math.abs(lit) - 1;
				
				boolean sign = lit > 0;
				
				if (bin_.getIth(var) == sign) {
					sat_count_[c]++;
				}
			    				
			} // for j

			if (sat_count_[c] == 0) unsat(c);
		} // for c

	} // init
	
	
	public void localSearch() {
		int flipvar;
		  
		for (step_ = 0; step_< max_flips_; step_++)	{
			
			if(unsat_stack_fill_pointer==0) return;		
			
			flipvar = cpick_skc(); // 

			flip_simp(flipvar);
		}
		
	} // local search
	

	/**
	 * Pick a best var to flip
	 * @return
	 */
	public int cpick_skc()	{			
		List<Integer>  truep;
		double eps = 1.0; 
		double cb = 2.165;
				
		int c = unsat_stack[PseudoRandom.randInt(0, unsat_stack_fill_pointer-1)];	// ���ѡ��һ����������Ӿ�			

		int [] breakValues = new int [constraints_.get(c).size()]; // ��¼C��ÿ��������breakֵ
		double [] f = new double [constraints_.get(c).size()]; // ����ÿ��������fֵ
		double sumF = 0.0;
		
		//the remaining vars
		for(int k = 0; k < constraints_.get(c).size(); ++k)	{
			int var = Math.abs(constraints_.get(c).get(k)) - 1; 
			
			if (bin_.getIth(var) == true) {
				truep = var_poslit_.get(var);
			} else {
				truep = var_neglit_.get(var);
			}		
		
			breakValues[k] = 0;
			
			int i;
			for (i = 0; i < truep.size();i++) {
				int ci = truep.get(i);
				
				if (sat_count_[ci] == 1) {					
					++breakValues[k];	
				}
			}
								
			f[k] = Math.pow(eps + breakValues[k], -cb);
			sumF = sumF + f[k];
		}
		
		
		for(int k = 0; k < constraints_.get(c).size(); ++k)	{
			f[k] = f[k]/sumF; // ����ѡ�����
		}
		
		double [] accumuProb = new double [f.length];
		
		
		accumuProb[0] = f[0] ;
		
		for(int k = 1; k < accumuProb.length; ++k)	{
			accumuProb[k] = accumuProb[k-1] + f[k]; // �����ۻ�����
		}
		
		// �����ۻ�����ѡ��һ������
		double  rnd = PseudoRandom.randDouble();
		int selected = -1;
		
		for(int k = 0; k < accumuProb.length; ++k)	{
			if (rnd <= accumuProb[k]) {
				selected = k; break;
			}
		}
				
		int rdnLit = constraints_.get(c).get(selected);

		return Math.abs(rdnLit) - 1;			
		
	}

	
	/**
	 * flip the var 
	 * @param flipvar
	 */
	void flip_simp(int flipvar)	{
		
		List<Integer> truep, falsep;
		
		if (bin_.getIth(flipvar) == true) {
			bin_.setIth(flipvar, false);
		} else {
			bin_.setIth(flipvar, true);
		}
				
		if (bin_.getIth(flipvar) == true) {
			truep  = var_poslit_.get(flipvar); 
			falsep = var_neglit_.get(flipvar);
		} else {
			truep  = var_neglit_.get(flipvar); 
			falsep = var_poslit_.get(flipvar);
		}
		
		for (int i = 0; i < truep.size(); i++){
			int ci = truep.get(i);
			++sat_count_[ci];
			if (sat_count_[ci] == 1) {
				 sat(ci); // sat_count from 0 to 1
			}
		}
		
		for (int i = 0; i < falsep.size(); i++){
			int ci = falsep.get(i);
			--sat_count_[ci];
			if (sat_count_[ci] == 0) {
				unsat(ci); //	last_unsatvar[c]=flipvar;
			}
		}
	}
	
	/**
	 * Add cluase into unsat stack
	 * @param clause
	 */
	public void unsat(int clause) {
		index_in_unsat_stack[clause] = unsat_stack_fill_pointer;
		push(clause,unsat_stack);
	}
	
	/**
	 * Push item into a stack
	 * @param item
	 * @param stack
	 */
	public void push(int item, int [] stack) {
		stack[unsat_stack_fill_pointer++] = item;
	}	
	
	
	public void sat(int clause)	{
		int index,last_unsat_clause;

		//since the clause is satisfied, its position can be reused to store the last_unsat_clause
		last_unsat_clause = pop(unsat_stack);
		index = index_in_unsat_stack[clause];
		unsat_stack[index] = last_unsat_clause;
		index_in_unsat_stack[last_unsat_clause] = index;
	}
	
	public int pop(int [] stack) {
		return stack[--unsat_stack_fill_pointer];
	}
	
	/**
	 * print solution variables
	 */
	public void printVar() {
		 int    i;
		  System.out.println("v ");;
		    for (i=0; i<num_vars_; i++) {
				if(bin_.getIth(i)==true) 
					System.out.print("1 ");
				else 
					System.out.print("0 ");
				
				if(i%10==0 && i!=0) 
				{
					System.out.println();
					System.out.print("v ");
				}
				else System.out.print(' ');
		     }
		    System.out.println("0 ");
	}
	/**
	 * Pick a best var to flip
	 * @return
	 */
	public int cpick_skc_test()	{			
		List<Integer>  truep,falsep;
					    	    
		int c = unsat_stack[PseudoRandom.randInt(0, unsat_stack_fill_pointer-1)];				
		int [] breakfalses = new int [constraints_.get(c).size()];
		
		//the first lit
		int lit = constraints_.get(c).get(0);
		
		// the first var 
		int var = Math.abs(lit) - 1;
		

		if (bin_.getIth(var) == true) {
			truep  = var_poslit_.get(var);
			falsep = var_neglit_.get(var);
		} else {
			truep  = var_neglit_.get(var);
			falsep = var_poslit_.get(var);
		}		
		
		// Calculte breakfalses
		int breakfalse = 0;
		for (int i = 0; i < falsep.size();i++) {		
			int ci = falsep.get(i);
			if (sat_count_[ci]==0) ++breakfalse;
		}	
		breakfalses[0] = breakfalse;		
		
		int bbreakv = 0;
		for (int i = 0; i < truep.size();i++) {
			int ci = truep.get(i);
			if (sat_count_[ci]==1) ++bbreakv;
		}			
		
		int best_bbreak = bbreakv;
		int [] bestvar_array = new int [constraints_.get(c).size()];
		bestvar_array[0] = var;
		int bestvar_count = 1;	
		
		//the remaining vars
		for(int k=1; k < constraints_.get(c).size(); ++k)	{
			var = Math.abs(constraints_.get(c).get(k)) - 1; 
				
			if (bin_.getIth(var) == true) {
				truep  = var_poslit_.get(var);
				falsep = var_neglit_.get(var);
			} else {
				truep  = var_neglit_.get(var);
				falsep = var_poslit_.get(var);
			}	
			
			// calcalute breakfalse
			breakfalse = 0;
			for (int i = 0; i < falsep.size();i++) {		
				int ci = falsep.get(i);
				if (sat_count_[ci]==0) ++breakfalse;
			}	
			breakfalses[k] = breakfalse	;
			
			// calculate bbreakv
			bbreakv=0;
			
			int i;
			for (i = 0; i < truep.size();i++) {
				int ci = truep.get(i);
				
				if (sat_count_[ci]==1) {
					if (bbreakv == best_bbreak) break;
					++bbreakv;	
				}
			}		
						
			if (i != truep.size() - 1) continue;
			
			if (bbreakv < best_bbreak)	{
				best_bbreak = bbreakv;
				bestvar_array[0] = var;
				bestvar_count = 1;
			}
			else {// if (bbreakv == best_bbreak)
			
				bestvar_array[bestvar_count]=var;
				++bestvar_count;
			}
		}
		
		if(best_bbreak == 0) 
			return bestvar_array[PseudoRandom.randInt(0,bestvar_count-1)];

		if( PseudoRandom.randDouble() < wp_) {
			int r = PseudoRandom.randInt(0,constraints_.get(c).size() - 1);
			int rdnLit = constraints_.get(c).get(r);			
			return Math.abs(rdnLit) - 1;
			
//			int bestBreakFalse =  breakfalses[0];
//			int bestBreakFalse_idx = 0;
//			
//			for (int i = 1; i < breakfalses.length; i++) {
//				if (breakfalses[i] >  bestBreakFalse) {
//					bestBreakFalse = breakfalses[i];
//					bestBreakFalse_idx = i;
//				}
//			}
//			return Math.abs(constraints_.get(c).get(bestBreakFalse_idx)) - 1;
			
		} else {
			return bestvar_array[PseudoRandom.randInt(0,bestvar_count-1)];
		}
		
	}
	/**
	 * A new break value for picking a best var to flip, which considers the number of false clauses become true
	 * @return
	 */
	public int cpick_skc_new()	{			
		List<Integer>  truep,falsep;
					    	    
		int c = unsat_stack[PseudoRandom.randInt(0, unsat_stack_fill_pointer-1)];				

		//the first lit
		int lit = constraints_.get(c).get(0);
		
		// the first var 
		int var = Math.abs(lit) - 1;
		
		if (bin_.getIth(var) == true) {
			truep  = var_poslit_.get(var);
			falsep = var_neglit_.get(var);
		} else {
			truep  = var_neglit_.get(var);
			falsep = var_poslit_.get(var);
		}		
		
		int bbreakv = 0;
		int breaktrue = 0;
		int breakfalse = 0;
		
		for (int i = 0; i < truep.size();i++) {
			int ci = truep.get(i);
			if (sat_count_[ci]==1) ++breaktrue;	
			
		}	
		
		for (int i = 0; i < falsep.size();i++) {		
			int ci = falsep.get(i);
			if (sat_count_[ci]==0) ++breakfalse;
		}	
				
		bbreakv  = breaktrue ;
				
		int best_bbreak = bbreakv;
		int [] bestvar_array = new int [constraints_.get(c).size()];
		int [] breakfalse_array = new int [constraints_.get(c).size()];
		bestvar_array[0] = var;
		breakfalse_array[0] =  breakfalse;
		int bestvar_count = 1;	
		
		//the remaining vars
		for(int k=1; k < constraints_.get(c).size(); ++k)	{
			var = Math.abs(constraints_.get(c).get(k)) - 1; 
			
			if (bin_.getIth(var) == true) {
				truep  = var_poslit_.get(var);
				falsep = var_neglit_.get(var);
			} else {
				truep  = var_neglit_.get(var);
				falsep = var_poslit_.get(var);
			}		
		
			
			breaktrue = 0;
			breakfalse = 0;
			
			int i;
			
			for (i = 0; i < truep.size();i++) {
				int ci = truep.get(i);		
				
				if (sat_count_[ci]==1) {
					if (breaktrue == best_bbreak) break;
					++breaktrue;	
				}
			}	
			
			if (i != truep.size() - 1) continue;
			
			for (i = 0; i < falsep.size();i++) {		
				int ci = falsep.get(i);
				if (sat_count_[ci]==0) ++breakfalse;
			}	
			
			bbreakv  = breaktrue;		
			
			if (bbreakv < best_bbreak)	{
				best_bbreak = bbreakv;
				bestvar_array[0] = var;
				breakfalse_array[0] =  breakfalse;
				bestvar_count = 1;
			}
			else {// if (bbreakv == best_bbreak)
			
				bestvar_array[bestvar_count] = var;
				breakfalse_array[bestvar_count] = breakfalse; 
				++bestvar_count;
			}
		}
							
		if(best_bbreak == 0) {
			return bestvar_array[PseudoRandom.randInt(0,bestvar_count-1)];
		}

		if( PseudoRandom.randDouble() < wp_) {
			int r = PseudoRandom.randInt(0,constraints_.get(c).size() - 1);
			int rdnLit = constraints_.get(c).get(r);
			
			return Math.abs(rdnLit) - 1;
		}
		else {
			int bestBreakFalse = breakfalse_array[0] ;
			int bestBreakFalse_idx = 0;
			
			for (int i = 1; i < bestvar_count; i++) {
				if (breakfalse_array[i] >  bestBreakFalse) {
					bestBreakFalse = breakfalse_array[i];
					bestBreakFalse_idx = i;
//					System.out.println(breakfalse_array[i]);
				}
			}
			return bestvar_array[bestBreakFalse_idx];
			
//			return bestvar_array[PseudoRandom.randInt(0,bestvar_count-1)];
		}
		
	}
	
	/**
	 * A new break value for picking a best var to flip, which considers the number of false clauses become true
	 * @return
	 */
	public int cpick_skc_new1()	{			
		List<Integer>  truep,falsep;
					    	    
		int c = unsat_stack[PseudoRandom.randInt(0, unsat_stack_fill_pointer-1)]; // ���ѡ��һ����������Ӿ�				
        
		int [] breakfalses = new int [constraints_.get(c).size()];
		//the first lit
		int lit = constraints_.get(c).get(0);
		
		// the first var 
		int var = Math.abs(lit) - 1;
		
		if (bin_.getIth(var) == true) {
			truep  = var_poslit_.get(var);
			falsep = var_neglit_.get(var);
		} else {
			truep  = var_neglit_.get(var);
			falsep = var_poslit_.get(var);
		}		
		
		int bbreakv = 0;	
		int breakfalse = 0;
		
		for (int i = 0; i < truep.size();i++) {
			int ci = truep.get(i);
			if (sat_count_[ci]==1) ++bbreakv;	
			
		}	
		
		for (int i = 0; i < falsep.size();i++) {		
			int ci = falsep.get(i);
			if (sat_count_[ci]==0) ++breakfalse;
		}	
		
		breakfalses[0] = 	breakfalse	;
				
		int best_bbreak = bbreakv;
		int [] bestvar_array = new int [constraints_.get(c).size()];
		int [] breakfalse_array = new int [constraints_.get(c).size()];
		bestvar_array[0] = var;
		breakfalse_array[0] =  breakfalse;
		int bestvar_count = 1;	
		
		//the remaining vars
		for(int k=1; k < constraints_.get(c).size(); ++k)	{
			var = Math.abs(constraints_.get(c).get(k)) - 1; 
			
			if (bin_.getIth(var) == true) {
				truep  = var_poslit_.get(var);
				falsep = var_neglit_.get(var);
			} else {
				truep  = var_neglit_.get(var);
				falsep = var_poslit_.get(var);
			}			
			
			bbreakv = 0;	
			breakfalse = 0;
			
			int i;
			
			for (i = 0; i < truep.size();i++) {
				int ci = truep.get(i);		
				
				if (sat_count_[ci]==1) {
					//if (bbreakv == best_bbreak) break;
					++bbreakv;	
				}
			}	
			
//			if (i != truep.size() - 1) continue;
			
			for (i = 0; i < falsep.size();i++) {		
				int ci = falsep.get(i);
				if (sat_count_[ci]==0) ++breakfalse;
			}	
			
			breakfalses[k] = breakfalse	;
		
			if (bbreakv < best_bbreak)	{
				best_bbreak = bbreakv;
				bestvar_array[0] = var;
				breakfalse_array[0] =  breakfalse;
				bestvar_count = 1;
			}
			else {// if (bbreakv == best_bbreak)
			
				bestvar_array[bestvar_count] = var;
				breakfalse_array[bestvar_count] = breakfalse; 
				++bestvar_count;
			}
		}
							
		if(best_bbreak == 0) {
//			int bestBreakFalse = breakfalse_array[0] ;
//			int bestBreakFalse_idx = 0;
//			
//			for (int i = 1; i < bestvar_count; i++) {
//				if (breakfalse_array[i] >  bestBreakFalse) {
//					bestBreakFalse = breakfalse_array[i];
//					bestBreakFalse_idx = i;
////					System.out.println(breakfalse_array[i]);
//				}
//			}
//			return bestvar_array[bestBreakFalse_idx];
			return bestvar_array[PseudoRandom.randInt(0,bestvar_count-1)];
		}

		if( PseudoRandom.randDouble() < wp_) {
			int r = PseudoRandom.randInt(0,constraints_.get(c).size() - 1);
			int rdnLit = constraints_.get(c).get(r);
			
			return Math.abs(rdnLit) - 1;
//			int bestBreakFalse =  breakfalses[0];
//			int bestBreakFalse_idx = 0;
//			
//			for (int i = 1; i < breakfalses.length; i++) {
//				if (breakfalses[i] >  bestBreakFalse) {
//					bestBreakFalse = breakfalses[i];
//					bestBreakFalse_idx = i;
//				}
//			}
//			return Math.abs(constraints_.get(c).get(bestBreakFalse_idx)) - 1;
		}
		else {
//			int bestBreakFalse = breakfalse_array[0] ;
//			int bestBreakFalse_idx = 0;
//			
//			for (int i = 1; i < bestvar_count; i++) {
//				if (breakfalse_array[i] >  bestBreakFalse) {
//					bestBreakFalse = breakfalse_array[i];
//					bestBreakFalse_idx = i;
//				}
//			}
//			return bestvar_array[bestBreakFalse_idx];
			
			return bestvar_array[PseudoRandom.randInt(0,bestvar_count-1)];
		}
		
	}
	
	/**
	 * A new break value for picking a best var to flip, which considers the number of false clauses become true
	 * @return
	 */
	public int cpick_skc_best()	{			
		List<Integer>  truep,falsep;
					    	    
		int c = unsat_stack[PseudoRandom.randInt(0, unsat_stack_fill_pointer-1)]; // ���ѡ��һ����������Ӿ�				
        
		int [] breakfalses = new int [constraints_.get(c).size()];
		//the first lit
		int lit = constraints_.get(c).get(0);
		
		// the first var 
		int var = Math.abs(lit) - 1;
		
		if (bin_.getIth(var) == true) {
			truep  = var_poslit_.get(var);
			falsep = var_neglit_.get(var);
		} else {
			truep  = var_neglit_.get(var);
			falsep = var_poslit_.get(var);
		}		
		
		int bbreakv = 0;	
		int breakfalse = 0;
		
		for (int i = 0; i < truep.size();i++) {
			int ci = truep.get(i);
			if (sat_count_[ci]==1) ++bbreakv;	
			
		}	
		
		for (int i = 0; i < falsep.size();i++) {		
			int ci = falsep.get(i);
			if (sat_count_[ci]==0) ++breakfalse;
		}	
		
		breakfalses[0] = 	breakfalse	;
				
		int best_bbreak = bbreakv;
		int [] bestvar_array = new int [constraints_.get(c).size()];
		bestvar_array[0] = var;
		int bestvar_count = 1;	
		
		//the remaining vars
		for(int k=1; k < constraints_.get(c).size(); ++k)	{
			var = Math.abs(constraints_.get(c).get(k)) - 1; 
			
			if (bin_.getIth(var) == true) {
				truep  = var_poslit_.get(var);
				falsep = var_neglit_.get(var);
			} else {
				truep  = var_neglit_.get(var);
				falsep = var_poslit_.get(var);
			}			
			
			bbreakv = 0;	
			breakfalse = 0;
			
			int i;
			
			for (i = 0; i < truep.size();i++) {
				int ci = truep.get(i);		
				
				if (sat_count_[ci]==1) {
//					if (bbreakv == best_bbreak) break;
					++bbreakv;	
				}
			}	
			
//			if (i != truep.size() - 1) continue;
			
			for (i = 0; i < falsep.size();i++) {		
				int ci = falsep.get(i);
				if (sat_count_[ci]==0) ++breakfalse;
			}	
			
			breakfalses[k] = breakfalse	;
		
			if (bbreakv < best_bbreak)	{
				best_bbreak = bbreakv;
				bestvar_array[0] = var;
				bestvar_count = 1;
			}
			else {// if (bbreakv == best_bbreak)			
				bestvar_array[bestvar_count] = var;
				++bestvar_count;
			}
		}
							
		if(best_bbreak == 0) {			
			return bestvar_array[PseudoRandom.randInt(0,bestvar_count-1)];
		}

		if( PseudoRandom.randDouble() < wp_) {
//			int bestBreakFalse =  breakfalses[0];
//			int bestBreakFalse_idx = 0;
//			
//			for (int i = 1; i < breakfalses.length; i++) {
//				if (breakfalses[i] >  bestBreakFalse) {
//					bestBreakFalse = breakfalses[i];
//					bestBreakFalse_idx = i;
//				}
//			}
//			return Math.abs(constraints_.get(c).get(bestBreakFalse_idx)) - 1;
			
			int r = PseudoRandom.randInt(0,constraints_.get(c).size() - 1);
			int rdnLit = constraints_.get(c).get(r);
			
			return Math.abs(rdnLit) - 1;
		}
		else {	
			return bestvar_array[PseudoRandom.randInt(0,bestvar_count-1)];
		}
		
	}
	
	  /**
     * Print basic data
     */
	public void printBasic() {
		System.out.println("# of vars = " + num_vars_);
		System.out.println("# of clauses = " + num_clauses_);
		System.out.println("# of featureIndicesAllowedFlip_ = " + featureIndicesAllowedFlip_.size());
		
		System.out.println("Pos---vID----Allowed v-----Clause ID--------begin");
		for (int v=0; v < num_vars_; ++v)    	{
//			String strToWrite = String.valueOf(v) + " " + (featureIndicesAllowedFlip_.get(v) + 1) + " ";
			String strToWrite = String.valueOf(v) + " ";
			for (int j = 0; j < var_poslit_.get(v).size();j++) {
				strToWrite = strToWrite + var_poslit_.get(v).get(j) + " ";
			}
			System.out.println(strToWrite);
			
    	}
		System.out.println("--------------------print poslit-----------end");
		
		System.out.println("Neg---vID----Allowed v-----Clause ID--------begin");
		for (int v=0; v < num_vars_; ++v)    	{
//			String strToWrite = String.valueOf(v) + " " + (featureIndicesAllowedFlip_.get(v) + 1) + " ";
			String strToWrite = String.valueOf(v) + " ";
			for (int j = 0; j < var_neglit_.get(v).size();j++) {
				strToWrite = strToWrite + var_neglit_.get(v).get(j) + " ";
			}
			System.out.println(strToWrite);
			
    	}
		System.out.println("--------------------print neglit-----------end");
	}
}
