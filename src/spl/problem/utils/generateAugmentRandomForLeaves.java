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
import java.util.ArrayList;
import java.util.List;
import java.util.StringTokenizer;

import jmetal.util.Configuration;
import jmetal.util.PseudoRandom;

public class generateAugmentRandomForLeaves {

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
		    fm = problemPath  +fm +  ".dimacs.leaves";  		          
            
	        BufferedReader in = new BufferedReader(new FileReader(fm));
	        String line;
	        while ((line = in.readLine()) != null) {
	            line = line.trim();

	            if (line.startsWith("c")) continue;
	            
	            // Read constraints
	            if (line.startsWith("p")) {
	                StringTokenizer st = new StringTokenizer(line, " ");
	                st.nextToken();
	                numFeatures = Integer.parseInt(st.nextToken());	
	                System.out.println("# features = " + numFeatures);
	                numLeaves = Integer.parseInt(st.nextToken());
	                System.out.println("# leaves = " + numLeaves);
	                continue;
	            }	             
	            
	            if (!line.isEmpty()) {
	            	leaves.add(Integer.parseInt(line));
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

	  	     int visitedLeaves = 0;
	  	     
	  	      for(int i = 1;i <= numFeatures;i ++){
	  	    	  
	  	    	  if (!leaves.contains((Integer)i)) {
	  	    		 strToWrite = String.valueOf(i) + " 0.0 0 0 0 0 0 0 0 0"; // 
	  	    	  
	  	    	  } else {
	  	    		  visitedLeaves ++;
	  	    		  
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
		  	    	  
		  	    	  if (visitedLeaves < 0.5 * leaves.size()) {
		  	    		  int accuracy = PseudoRandom.randInt(1, 10);	// [1,10], min		  	    	  
			  	    	  strToWrite = strToWrite + String.valueOf(accuracy) + " 0";	
		  	    	  } else {
		  	    		  double accuracyFactor = PseudoRandom.randDouble(0.0, 2.0);	// [0,2], max		  	    	  
			  	    	  strToWrite = strToWrite + "0 " + String.valueOf(accuracyFactor);	
		  	    	  }		  	    		  
		  	    	  
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
	  * The main method
	  * @param args
	 * @throws Exception 
	  */
	 public static void main(String args[]) throws Exception {
		 String [] fm = {
//					"BerkeleyDB",	
//					"Drupal",
//					"Amazon",
//					"ERS",
//					"E-shop",
//					"Random-10000",
//					"WebPortal",
//					"printers",
//					"ubuntu1410",
//					"windows80",
//					"BigDataSystem",
				 
					"SubseaControlSystem",
					"FQAs",
					"windows70",
					"EIS",
					"Ubuntu1204",
					"android510",
					"BankingSoftware",
					
//				 	"SPLOT-3CNF-FM-500-50-1.00-SAT-1",
//					"SPLOT-3CNF-FM-500-50-1.00-SAT-2",
//					"SPLOT-3CNF-FM-500-50-1.00-SAT-3",
//					"SPLOT-3CNF-FM-500-50-1.00-SAT-4",
//					"SPLOT-3CNF-FM-500-50-1.00-SAT-5",
//					"SPLOT-3CNF-FM-500-50-1.00-SAT-6",
//					"SPLOT-3CNF-FM-500-50-1.00-SAT-7",
//					"SPLOT-3CNF-FM-500-50-1.00-SAT-8",
//					"SPLOT-3CNF-FM-500-50-1.00-SAT-9",
//					"SPLOT-3CNF-FM-500-50-1.00-SAT-10",
////					//---------------------------
//					"SPLOT-3CNF-FM-1000-100-1.00-SAT-1",
//					"SPLOT-3CNF-FM-1000-100-1.00-SAT-2",
//					"SPLOT-3CNF-FM-1000-100-1.00-SAT-3",
//					"SPLOT-3CNF-FM-1000-100-1.00-SAT-4",
//					"SPLOT-3CNF-FM-1000-100-1.00-SAT-5",
//					"SPLOT-3CNF-FM-1000-100-1.00-SAT-6",
//					"SPLOT-3CNF-FM-1000-100-1.00-SAT-7",
//					"SPLOT-3CNF-FM-1000-100-1.00-SAT-8",
//					"SPLOT-3CNF-FM-1000-100-1.00-SAT-9",
//					"SPLOT-3CNF-FM-1000-100-1.00-SAT-10",
////					//---------------------------
//					"SPLOT-3CNF-FM-2000-200-0.50-SAT-1",
//					"SPLOT-3CNF-FM-2000-200-0.50-SAT-2",
//					"SPLOT-3CNF-FM-2000-200-0.50-SAT-3",
//					"SPLOT-3CNF-FM-2000-200-0.50-SAT-4",
//					"SPLOT-3CNF-FM-2000-200-0.50-SAT-5",
//					"SPLOT-3CNF-FM-2000-200-0.50-SAT-6",
//					"SPLOT-3CNF-FM-2000-200-0.50-SAT-7",
//					"SPLOT-3CNF-FM-2000-200-0.50-SAT-8",
//					"SPLOT-3CNF-FM-2000-200-0.50-SAT-9",
//					"SPLOT-3CNF-FM-2000-200-0.50-SAT-10",				
////					//---------------------------
//					"SPLOT-3CNF-FM-5000-500-0.30-SAT-1",
//					"SPLOT-3CNF-FM-5000-500-0.30-SAT-2",
//					"SPLOT-3CNF-FM-5000-500-0.30-SAT-3",
//					"SPLOT-3CNF-FM-5000-500-0.30-SAT-4",
//					"SPLOT-3CNF-FM-5000-500-0.30-SAT-5",
//					"SPLOT-3CNF-FM-5000-500-0.30-SAT-6",
//					"SPLOT-3CNF-FM-5000-500-0.30-SAT-7",
//					"SPLOT-3CNF-FM-5000-500-0.30-SAT-8",
//					"SPLOT-3CNF-FM-5000-500-0.30-SAT-9",
//					"SPLOT-3CNF-FM-5000-500-0.30-SAT-10",
//					//---------------------------
//					"SPLOT-3CNF-FM-10000-1000-0.10-SAT-1",
//					"SPLOT-3CNF-FM-10000-1000-0.10-SAT-2",
//					"SPLOT-3CNF-FM-10000-1000-0.10-SAT-3",
//					"SPLOT-3CNF-FM-10000-1000-0.10-SAT-4",
//					"SPLOT-3CNF-FM-10000-1000-0.10-SAT-5",
//					"SPLOT-3CNF-FM-10000-1000-0.10-SAT-6",
//					"SPLOT-3CNF-FM-10000-1000-0.10-SAT-7",
//					"SPLOT-3CNF-FM-10000-1000-0.10-SAT-8",
//					"SPLOT-3CNF-FM-10000-1000-0.10-SAT-9",
//					"SPLOT-3CNF-FM-10000-1000-0.10-SAT-10",
				 		
				   };
		 
		 for (int i = 0; i  < fm.length;i++) {
			 generateAugmentRandomForLeaves ga = new generateAugmentRandomForLeaves();
			 ga.loadFM(fm[i]);
			 ga.writeAugments(fm[i]);
			 System.out.println("Write " + fm[i] + " augment to file done!!");
		 }
		
	 }
}
