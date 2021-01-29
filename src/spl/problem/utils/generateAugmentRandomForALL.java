 /**
  * This class generates augments for a given SPL problem in a random way 
  * Only leaves are augmented with attributes, and non-leaf features are with 0 or 1 attribute values
  */
package SPL.problem.util;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;
import java.util.StringTokenizer;

import jmetal.util.Configuration;
import jmetal.util.PseudoRandom;

public class generateAugmentRandomForALL {

	private int numFeatures; // how many features
	private int numLeaves; // how many leaves
	private String problemPath = "./splotfm/";
    public  List<Integer> leaves = new ArrayList<Integer>(); // can be static 
    
    
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
	  	      
	  	      strToWrite = "#Feature_index cost used_before defects memory latency cycle accuracy accuracyFactor";	  	   
	  	      bw.write(strToWrite);
	  	      bw.newLine();

	  	     int visitedNode = 0;
	  	     
	  	      for(int i = 1;i <= numFeatures;i ++){	  	    	  

	  	    	  visitedNode ++;
	  	    		  
	  	    	  strToWrite = String.valueOf(i) + " ";		  	    	  
	  	    	  double cost = PseudoRandom.randDouble(1.0, 500.0); // [1,500], sum	  	    	  
	  	    	  strToWrite = strToWrite + String.valueOf(cost) + " ";		
	  	    	  
	  	    	  int usedBefore = PseudoRandom.randDouble() < 0.5 ? 1:0;		  	    			  
	  	    	  strToWrite = strToWrite + String.valueOf(usedBefore) + " ";		  	    		  	    
	  	    	  
	  	    	  int DEFECTS = PseudoRandom.randInt(0, 10);		  	    	  
	  	    	  strToWrite = strToWrite + String.valueOf(DEFECTS) + " ";
	  	    	  
	  	    	  int memory = PseudoRandom.randInt(1, 512); // [1,512], sum		  	    	  
	  	    	  strToWrite = strToWrite + String.valueOf(memory) + " ";	
	  	    	  
	  	    	  int latency = PseudoRandom.randInt(200, 800); // [200,800], min			  	    	  
	  	    	  strToWrite = strToWrite + String.valueOf(latency) + " ";	
	  	    	  
	  	    	  int Cycle = PseudoRandom.randInt(10, 500);	// [10,500], max		  	    	  
	  	    	  strToWrite = strToWrite + String.valueOf(Cycle) + " ";	
	  	    	  
	  	    	  if (visitedNode < 0.5 * numFeatures) {
	  	    		  int accuracy = PseudoRandom.randInt(1, 10);	// [1,10], min		  	    	  
		  	    	  strToWrite = strToWrite + String.valueOf(accuracy) + " 0";	
	  	    	  } else {
	  	    		  double accuracyFactor = PseudoRandom.randDouble(0.0, 2.0);	// [0,2], max		  	    	  
		  	    	  strToWrite = strToWrite + "0 " + String.valueOf(accuracyFactor);	
	  	    	  }		
	  	    	  
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
	  * write Leaves into default file
	  */
	 public void writeLeaves(String fm) {
		 String filePath =  problemPath  + fm +  ".dimacs.leaves";  
		 
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
	  	      
	  	      strToWrite = "p " + numFeatures + " " + numFeatures;	
	  	      bw.write(strToWrite);
	  	      bw.newLine();
	  	      
			  for (int i = 1; i <= numFeatures;i++) {	
		  	    	 bw.write(String.valueOf(i));
		  	    	 bw.newLine();
			  }
			  
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
				    "toybox", // 
		    		"axTLS", 	    		
		    	
		    		"fiasco",	 
					"uClinux",    
					"busybox-1.18.0",  
	
					"2.6.28.6-icse11",				
					"freebsd-icse11",  
					"uClinux-config",  
		     		"buildroot",  
		     		"freetz",   
		    		"coreboot", 		
					"2.6.32-2var", 
		    		"2.6.33.3-2var",
				 		
				   };
		 
		 for (int i = 0; i  < fm.length;i++) {
			 generateAugmentRandomForALL ga = new generateAugmentRandomForALL();
			 ga.loadFM(fm[i]);
			 ga.writeAugments(fm[i]);
			 ga.writeLeaves(fm[i]);
			 System.out.println("Write " + fm[i] + " augment to file done!!");
		 }
		
	 }
}
