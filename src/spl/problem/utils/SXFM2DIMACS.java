/**
 * This class convent FMs in SXFM formation to dimacs format
 * and write leaves into files
 * Coded by Yi Xiang (gzhuxiang_yi@163.com) 
 * @ 2017/7/24
 * Please note that since the root must be selected, it is used as a constraint when converting. 
 * Thus, the number of constraints is larger than the original by 1
 */
package spl.problem.utils;

import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import jmetal.util.Configuration;
import splar.core.constraints.BooleanVariableInterface;
import splar.core.constraints.CNFClause;
import splar.core.constraints.CNFFormula;
import splar.core.constraints.CNFLiteral;
import splar.core.constraints.PropositionalFormula;
import splar.core.fm.FeatureGroup;
import splar.core.fm.FeatureModel;
import splar.core.fm.FeatureModelStatistics;
import splar.core.fm.FeatureTreeNode;
import splar.core.fm.RootNode;
import splar.core.fm.SolitaireFeature;
import splar.core.fm.XMLFeatureModel;

public class SXFM2DIMACS {

	 String problemPath = "./all_FM/";
	 FeatureModel featureModel; 
	 CNFFormula cnf;
	 Map<String, Integer>  variable2indexMap;
	 static int id ;
	 
	 public void parse(String fm) {
		 id = 1;
		 String readPath = problemPath + fm + ".xml";
		 String writePath = problemPath + fm + ".dimacs";
		 String writeLeavesPath = problemPath + fm + ".dimacs.leaves";
		 try {
			/*
			 * Creates the Feature Model Object ********************************
			 * - Constant USE_VARIABLE_NAME_AS_ID indicates that if an ID has
			 * not been defined for a feature node in the XML file the feature
			 * name should be used as the ID. - Constant SET_ID_AUTOMATICALLY
			 * can be used to let the system create an unique ID for feature
			 * nodes without an ID specification Note: if an ID is specified for
			 * a feature node in the XML file it will always prevail
			 */
			 // Read xml file from the readPath
			featureModel = new XMLFeatureModel(readPath, XMLFeatureModel.USE_VARIABLE_NAME_AS_ID);

			// Load the XML file and creates the feature model
			featureModel.loadModel();					
			 
			variable2indexMap = new HashMap<String,Integer>();					
						
			traverseDFS(featureModel.getRoot(), 0); // To initialize variable2indexMap 
			
//			System.out.println("id = " + id);
			/**
			 * For each Variable, map its ID to an integer (starting from 1) to fit the dimacs format
			 */
			// Convent it to cnf format 
			cnf = featureModel.FM2CNF(); // 
											
			// Step 1: Write variables
			writeVarialbes(writePath);
			// Step 2: Write CNF constraints including derived and CTCs
			writeConstraints(writePath);
				
			System.out.println("# Variables " + cnf.getVariables().size());
			System.out.println("# Clauses " + cnf.getClauses().size());
						
			
			// Print leaves	
//			for (FeatureTreeNode node : featureModel.getLeaves()) {
//				System.out.println(variable2indexMap.get(node.getID()));
//			}
			// Step 3: write leaves
			writeLeaves(writeLeavesPath);
			//
			System.out.println("===============Feature statistics ===============");
			printStatistics(featureModel);
			System.out.println("===============Feature statistics ===============");
		} catch (Exception e) {
			e.printStackTrace();
		}

	}	 
	 
	/**
	 * @param featureModel
	 */
	private void printStatistics(FeatureModel featureModel) {
		// Now, let's traverse the extra constraints as a CNF formula
		System.out.println("EXTRA CONSTRAINTS ---------------------------");
		traverseConstraints(featureModel);

		// Now, let's print some statistics about the feature model
		FeatureModelStatistics stats = new FeatureModelStatistics(featureModel);
		stats.update();

		stats.dump();

	}
	
	public void traverseConstraints(FeatureModel featureModel) {
		for (PropositionalFormula formula : featureModel.getConstraints()) {
			System.out.println(formula);
		}
	}
	
	public void displayStandOut() {
		for (Iterator<BooleanVariableInterface> it = cnf.getVariables().iterator(); it.hasNext();) {				
            String variableID= it.next().getID();
			System.out.println(variableID + "," + variable2indexMap.get(variableID));
		}
		
		
		/** 
		 * Visit each clause
		 */	
		
		for (Iterator<CNFClause> it = cnf.getClauses().iterator(); it.hasNext();) {				
			CNFClause cnfc = it.next(); // for each clause
			
			for (Iterator<CNFLiteral> it2 = ((CNFClause)cnfc).getLiterals().iterator(); it2.hasNext();) { // for each literal
				CNFLiteral literal = it2.next();
				String variableID= literal.getVariable().getID();
						
				if (literal.isPositive()) {
					System.out.print( variable2indexMap.get(variableID) + " ");
				} else {
					System.out.print( "-" + variable2indexMap.get(variableID) + " ");
				}
			}
			
			System.out.println();
		}			
	
	}
	 /**
	  * Write variables into default file
	  */
	 public void writeVarialbes(String filePath) {		
		 
		 try {
	  	      /* Open the file */
	  	      FileOutputStream fos   = new FileOutputStream(filePath,false)     ;
	  	      OutputStreamWriter osw = new OutputStreamWriter(fos)    ;
	  	      BufferedWriter bw      = new BufferedWriter(osw)        ;
	  	    
	  	      String strToWrite;
	  	      
//	  	      strToWrite = "c This dimacs file is created from sxfm (.xml) by SXFM.JAR";	  	   
//	  	      bw.write(strToWrite);
//	  	      bw.newLine();
//	  	      
//	  	      strToWrite = "c Author: Yi Xiang (gzhuxiang_yi@163.com)";	  	   
//	  	      bw.write(strToWrite);
//	  	      bw.newLine();
//	  	      
//	  	      SimpleDateFormat df = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss");//
//	  	      strToWrite = "c Time: " + df.format(new Date());	
//	  	      bw.write(strToWrite);
//	  	      bw.newLine();
	  	    
	  	      List <Integer> intID = new ArrayList<Integer>(cnf.getVariables().size());
	  	      List <String> name = new ArrayList<String>(cnf.getVariables().size());
				
	  	      
	  	      for(int i=0;i<cnf.getVariables().size();i++) {
	  	    	intID.add(i);
	  	    	name.add(null);
	  	      }
	  	     
	  	      for (Iterator<BooleanVariableInterface> it = cnf.getVariables().iterator(); it.hasNext();) {				
				    String variableID= it.next().getID(); // name				
					intID.set(variable2indexMap.get(variableID) - 1, variable2indexMap.get(variableID));
					name.set(variable2indexMap.get(variableID) - 1,variableID);					
			  }	
	  	    
	  	      
		  	  for (int i=0;i<intID.size();i++) {
					strToWrite = "c " +  intID.get(i) + " " + name.get(i);
					bw.write(strToWrite);
		  	    	bw.newLine();
			  }		 
	  	      		  	 
	  	  
		  	  strToWrite = "p cnf " + cnf.getVariables().size() + " " + (cnf.getClauses().size() );		  	
			  bw.write(strToWrite);
	  	      bw.newLine();
	  	      
	  	      /* Close the file */
	  	      bw.close();
	  	    }catch (IOException e) {
	  	      Configuration.logger_.severe("Error acceding to the file");
	  	      e.printStackTrace();
	  	    }//catch
	 }
	 
	 
	 /**
	  * Write variables into default file
	  */
	 public void writeConstraints(String filePath) {		
		 
		 try {
	  	      /* Open the file */
	  	      FileOutputStream fos   = new FileOutputStream(filePath,true)     ;
	  	      OutputStreamWriter osw = new OutputStreamWriter(fos)    ;
	  	      BufferedWriter bw      = new BufferedWriter(osw)        ;
	  	    
	  	    
	  	    /** 
			 * Visit each clause
			 */	
			
			for (Iterator<CNFClause> it = cnf.getClauses().iterator(); it.hasNext();) {				
				CNFClause cnfc = it.next(); // for each clause
				
				String strToWrite = "";
				 
				for (Iterator<CNFLiteral> it2 = ((CNFClause)cnfc).getLiterals().iterator(); it2.hasNext();) { // for each literal
					CNFLiteral literal = it2.next();
					String variableID= literal.getVariable().getID();
							
					if (literal.isPositive()) {
						strToWrite = strToWrite + variable2indexMap.get(variableID) + " ";
					} else {
						strToWrite = strToWrite + "-" + variable2indexMap.get(variableID) + " ";
					}
					
				} // for 
				
				strToWrite = strToWrite + "0";
				bw.write(strToWrite);
		  	    bw.newLine();
			  }	// for 		
		  	  
	  	      /* Close the file */
	  	      bw.close();
	  	    }catch (IOException e) {
	  	      Configuration.logger_.severe("Error acceding to the file");
	  	      e.printStackTrace();
	  	    }//catch
	 }
		
	 /**
	  * Deep first search for marking nodes
	  * @param node
	  * @param tab
	  */
	 public void traverseDFS(FeatureTreeNode node, int tab) {
			for( int j = 0 ; j < tab ; j++ ) {
				System.out.print("\t");
			}

			boolean flag = true;
			
			// Root Feature
			if ( node instanceof RootNode ) {
				System.out.print("Root");
			}
			// Solitaire Feature
			else if ( node instanceof SolitaireFeature ) {
				// Optional Feature
				if ( ((SolitaireFeature)node).isOptional()) {
					System.out.print("Optional");
				}
				// Mandatory Feature
				else {
					System.out.print("Mandatory");
				}
			}
			// Feature Group
			else if ( node instanceof FeatureGroup ) {
				int minCardinality = ((FeatureGroup)node).getMin();
				int maxCardinality = ((FeatureGroup)node).getMax();
				System.out.print("Feature Group[" + minCardinality + "," + maxCardinality + "]"); 
				flag = false;
			}
			// Grouped feature
			else {
				System.out.print("Grouped"); 
			}
		
			if (flag == true) {
				System.out.print( "(ID=" + node.getID() + "," + id + ", NAME=" + node.getName() + ")\r\n");
				variable2indexMap.put(node.getID(), id);
	            id ++;	           
			} else {
				System.out.print( "(ID=" + node.getID() + ", NAME=" + node.getName() + ")\r\n");
			}
			
			for( int i = 0 ; i < node.getChildCount() ; i++ ) {		
				traverseDFS((FeatureTreeNode)node.getChildAt(i), tab+1);
			}
			
		}

	 
	 /**
	  * write Leaves into default file
	  */
	 public void writeLeaves(String filePath) {
				 
		 try {
	  	      /* Open the file */
	  	      FileOutputStream fos   = new FileOutputStream(filePath,false)     ;
	  	      OutputStreamWriter osw = new OutputStreamWriter(fos)    ;
	  	      BufferedWriter bw      = new BufferedWriter(osw)        ;
	  	    
	  	      String strToWrite;
	  	      
	  	      strToWrite = "c This leaves file is created from sxfm (.xml) by SXFM.JAR";	  	   
	  	      bw.write(strToWrite);
	  	      bw.newLine();
	  	      
	  	      strToWrite = "c Author: Yi Xiang (gzhuxiang_yi@163.com)";	  	   
	  	      bw.write(strToWrite);
	  	      bw.newLine();
	  	      
	  	      SimpleDateFormat df = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss");//
	  	      strToWrite = "c Time: " + df.format(new Date());	
	  	      bw.write(strToWrite);
	  	      bw.newLine();
	  	      
	  	      strToWrite = "c Format: p number of total features number of leaves";	
	  	      bw.write(strToWrite);
	  	      bw.newLine();
	  	      
	  	      strToWrite = "p " + cnf.getVariables().size() + " " + featureModel.getLeaves().size();	
	  	      bw.write(strToWrite);
	  	      bw.newLine();
	  	      
			  for (FeatureTreeNode node : featureModel.getLeaves()) {	
		  	    	 bw.write(String.valueOf(variable2indexMap.get(node.getID())));
		  	    	 bw.newLine();
			  }
			  
	  	      /* Close the file */
	  	      bw.close();
	  	    }catch (IOException e) {
	  	      Configuration.logger_.severe("Error acceding to the file");
	  	      e.printStackTrace();
	  	    }//catch
	 }
	 
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		String [] fm = {
//				"Cellphone",
//				"CounterStrikeSimpleFeatureModel",
//				"SPLSSimuelESPnP",
//				"DSSample",
//				"ElectronicDrum",
//				"SmartHomev2.2",
//				"VideoPlayer",
//				"ModelTransformation",
//				"CocheEcologico",
//				"Printers",
//				"Drupal",
//				"Amazon",
//				"WebPortal",
//				"E-shop",
//				"BerkeleyDB",
//				"SPLOT-3CNF-FM-5000-1000-0,30-SAT-1",
//				"SPLOT-3CNF-FM-1000-200-0,50-SAT-1",
//				"SPLOT-3CNF-FM-1000-200-0,50-SAT-2",
//				"SPLOT-3CNF-FM-1000-200-0,50-SAT-3",
//				"SPLOT-3CNF-FM-1000-200-0,50-SAT-4",
//				"SPLOT-3CNF-FM-1000-200-0,50-SAT-5",
//				"SPLOT-3CNF-FM-1000-200-0,50-SAT-6",
//				"SPLOT-3CNF-FM-1000-200-0,50-SAT-7",
//				"SPLOT-3CNF-FM-1000-200-0,50-SAT-8",
//				"SPLOT-3CNF-FM-1000-200-0,50-SAT-9",
//				"SPLOT-3CNF-FM-1000-200-0,50-SAT-10",
				"Automotive02_V1",
//				"Automotive02_V2",
//				"Automotive02_V3",
//				"Automotive02_V4",
//				"2017-05-22",
//				"2017-09-28",
//				"2017-10-20",
//				"2017-11-20",
//				"2017-12-22",
//				"2018-01-23",
//				"2018-02-20",
//				"2018-03-26",
//				"2018-04-23",
//				"2018-05-09",
				
				// 以下三个模型不用转换
//				"ecos-icse11",
//				"freebsd-icse11",
//				"2.6.28.6-icse11",		
		       };

		for (int i = 0; i  < fm.length;i++) {
			 SXFM2DIMACS sxfm2dimacs = new SXFM2DIMACS();
			 sxfm2dimacs.parse(fm[i]);			
			 System.out.println("Write " + fm[i] + " augment to file done!!");
		}
	}

}
