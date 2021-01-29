/**
 * This class finds rich seeds for FMs from the results of existing algorithms
 * A rich seed has as many as selected features as possible
 * @author Yi Xiang
 * @ Time 2017/7/26
 * @ Yi Xiang
 */
package spl.problem.utils;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.OutputStreamWriter;

import jmetal.util.Configuration;
import jmetal.util.JMException;

/**
 * @author Administrator
 *
 */
public class findRichSeed {
	private String experimentName_ ;
	private String[] algName_;
	private String[] problemNames_;
	private int numberofRuns_ ;
	private int objectives_;
	/**
	 * 
	 */
	public findRichSeed(String experimentName,String[] problemNames, int numberofRuns,
			String[] algName,int objectives) {
		
		experimentName_ = experimentName;
		problemNames_ = problemNames;
		numberofRuns_ = numberofRuns;	
		algName_ = algName;	
		objectives_ = objectives;
		// TODO Auto-generated constructor stub
	}
	
	/**
	 * @param args
	 * @throws JMException 
	 * @throws ClassNotFoundException 
	 * @throws InterruptedException 
	 * @throws MatlabConnectionException 
	 * @throws MatlabInvocationException 
	 */
	public static void main(String[] args) throws JMException, ClassNotFoundException, InterruptedException {
		String [] algNames = new String[]{
				/**
				 * Used in SATVaEAStudyRevise study
				 */		

	    		"SATVaEA",  // 	    	
	    		
		};
		
		String [] problemNames = new String[]{
//	    		"BerkeleyDB", 
//	    		"ERS","WebPortal","E-shop","Drupal","Amazon",
//	    		"Random-10000",
				"RealAmazon",
	    		"RealDrupal",
		};
				
		/*
		 * The following should be tuned manually
		 */
		int objectives = 4;		// 
		String experimentName = "./Experiment/SATVaEAStudyRevise/";
		
		int numberofRuns = 30;		
		
		/*
		 * End
		 */
		
		findRichSeed frs = new findRichSeed(experimentName,problemNames,numberofRuns, algNames,objectives);				
		
		try {
			frs.execute();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}								

	} // main
	
	/**
	 * Execute 
	 * @throws ClassNotFoundException
	 * @throws InterruptedException 
	 * @throws IOException 
	 */
	
	 public void execute() throws ClassNotFoundException, InterruptedException, IOException{				
		 
		 for (int i = 0;i < problemNames_.length;i++) { // for each problem
			 String bestSeed = "" ;
			 int maxFeatures = -1;
			 
			 for (int k = 0; k < algName_.length;k++){ // for each algorithm
				 
				 for (int r = 0; r < this.numberofRuns_; r ++) { // for each run
					 String path = experimentName_ + "/data/" + algName_[k] + "/" + problemNames_[i]+"/VAR." + r;
					 
						BufferedReader in = new BufferedReader(new FileReader(path));
				        String line;				        
				       
				        while ((line = in.readLine()) != null) {
				           line = line.trim();	
				           int sum = 0;
				           for (int len = 0; len < line.length();len++) {	
				        	   sum += Integer.parseInt(line.substring(len, len + 1));
				           }
				
				           if (sum > maxFeatures) {
				        	   maxFeatures = sum;
				        	   bestSeed = new String(line);				        	
				           }
				         
				         
				        } // while				       
				        in.close(); 
				 } //for r
			 } // for k
			 System.out.println("bestSeed = " + bestSeed);
			 
			 String writePath = "./SIPFMs/" + problemNames_[i] + ".dimacs.richseed";
		
			 try {
		  	      /* Open the file */
		  	      FileOutputStream fos   = new FileOutputStream(writePath,false)     ;
		  	      OutputStreamWriter osw = new OutputStreamWriter(fos)    ;
		  	      BufferedWriter bw      = new BufferedWriter(osw)        ;
		  	    
		  	      String strToWrite = "";  
		  	    
		  	      for(int idx = 0;idx < bestSeed.length();idx ++){		  	    	 
		  	    	  
		  	    	  if (Integer.parseInt(bestSeed.substring(idx, idx + 1)) == 1) {
		  	    		strToWrite += String.valueOf(idx + 1) + " ";
		  	    	  } else {
		  	    		strToWrite += String.valueOf(-(idx + 1)) + " ";
		  	    	  }		  	    	  
		  	    	 
		  	      }      	   
		  	      System.out.println(strToWrite);
		  	      bw.write(strToWrite);	  	    	 
		  	      /* Close the file */
		  	      bw.close();
		  	      
		  	    }catch (IOException e) {
		  	      Configuration.logger_.severe("Error acceding to the file in findRichSeed!!");
		  	      e.printStackTrace();
		  	    }//catch
			
		 } // for i
		 
    	
    	
	 }//execute

	 public String getExperimentName_() {
			return experimentName_;
		}

		public void setExperimentName_(String experimentName_) {
			this.experimentName_ = experimentName_;
		}

		public String[] getAlgName_() {
			return algName_;
		}

		public void setAlgName_(String[] algName_) {
			this.algName_ = algName_;
		}
			
		
		public int getNumberofRuns_() {
			return numberofRuns_;
		}

		public void setNumberofRuns_(int numberofRuns_) {
			this.numberofRuns_ = numberofRuns_;
		}			
	
	
	
	 } // class
