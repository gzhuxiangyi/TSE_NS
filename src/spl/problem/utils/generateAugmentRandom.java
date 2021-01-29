 /**
  * This class generates augments for a given SPL problem in a random way 
  */
package SPL.problem.util;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.StringTokenizer;

import jmetal.util.Configuration;
import jmetal.util.PseudoRandom;

public class generateAugmentRandom {

	int numFeatures; // how many features
    String problemPath = "./linux-variability-analysis-tools.formulas/";
	/**
	 * 
	 * @param fm
	 * @param augment
	 * @throws Exception
	 */
	 public void loadFM(String fm) throws Exception {
		    fm = problemPath  +fm +  ".dimacs";  
	        BufferedReader in = new BufferedReader(new FileReader(fm));
	        String line;
	        while ((line = in.readLine()) != null) {
	            line = line.trim();

	            // Read constraints
	            if (line.startsWith("p")) {
	                StringTokenizer st = new StringTokenizer(line, " ");
	                st.nextToken();
	                st.nextToken();
	                numFeatures = Integer.parseInt(st.nextToken());	      
	                break;
	            }	           
	        } // while
	        
	        in.close(); 
	 }
	 /**
	  * write augments into default file
	  */
	 public void writeAugments(String fm) {
		 String filePath =  problemPath  + fm +  ".dimacs.augment";  
		 
		 try {
	  	      /* Open the file */
	  	      FileOutputStream fos   = new FileOutputStream(filePath,false)     ;
	  	      OutputStreamWriter osw = new OutputStreamWriter(fos)    ;
	  	      BufferedWriter bw      = new BufferedWriter(osw)        ;
	  	    
	  	      String strToWrite;
	  	      
	  	      strToWrite = "#FEATURE_INDEX COST USED_BEFORE DEFECTS";	  	   
	  	      bw.write(strToWrite);
	  	      bw.newLine();
	  	    
	  	      for(int i = 1;i <= numFeatures;i ++){
	  	    	  strToWrite = String.valueOf(i) + " ";
	  	    	  
	  	    	  double cost = PseudoRandom.randDouble(5.0, 15.0);
	  	    	  
	  	    	  strToWrite = strToWrite + String.valueOf(cost) + " ";
	  	    	  
	  	    	  int usedBefore = PseudoRandom.randDouble() < 0.5 ? 1:0;
	  	    			  
	  	    	  strToWrite = strToWrite + String.valueOf(usedBefore) + " ";
	  	    		  	    
	  	    	  int DEFECTS = PseudoRandom.randInt(0, 10);
	  	    	  
	  	    	  strToWrite = strToWrite + String.valueOf(DEFECTS) + " ";
	  	    	  
	  	    	  bw.write(strToWrite);
	  	    	  bw.newLine();
	  	      }      	     
//	  	      bw.newLine();    
	  	      /* Close the file */
	  	      bw.close();
	  	    }catch (IOException e) {
	  	      Configuration.logger_.severe("Error acceding to the file");
	  	      e.printStackTrace();
	  	    }//catch
	 }
	 /**
	  * The main method
	  * @param args
	 * @throws Exception 
	  */
	 public static void main(String args[]) throws Exception {
		 String [] fm = {
				 		"phone",
//				 		"axTLS", "2.6.32-2var", "buildroot",
//				         "busybox-1.18.0","coreboot","embtoolkit",
//				         "freetz", "toybox", "uClinux-config","2.6.33.3-2var"
				         };
		 
		 for (int i = 0; i  < fm.length;i++) {
			 generateAugmentRandom ga = new generateAugmentRandom();
			 ga.loadFM(fm[i]);
			 ga.writeAugments(fm[i]);
			 System.out.println("Write " + fm[i] + " augment to file done!!");
		 }
		
	 }
}
