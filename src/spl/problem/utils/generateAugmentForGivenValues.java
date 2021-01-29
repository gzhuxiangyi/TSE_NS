 /**
  * This class generates augments for a given SPL problem for a given set of values
  * For example, cost, defects, not used are copied from other files
  * double cost[] = {10.2,14.0,5.2,5.7,12.2,4.2,3.5,9.2,19.9,17.9,14.0,18.2,5.9};
  * int defects[] = {9,8,10,0,0,5,4,4,0,3,0,0,4};
  * int not_used[] = {0,0,0,1,1,0,0,0,1,0,1,1,0};
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

public class generateAugmentForGivenValues {

	/**
	 * For a general FM
	 */
	  double cost[] ;
	  int defects[] ;
	  int not_used[] ;
	  
	  /**
	   * For RealAmazon
	   */
	  int costMonth[] = {10623,104,10671,3950,1916,3634,13509,1578,16159,4474,1898,5501,18053,10142,10942,6255,8715,7959,11615,12334,5847,1415,4277,6446,11825,1235,6441,11844,5441,6082,3402,7406,10970,16738,13576,2151,18095,8388,3479,7890,11928,217,6804,14264,13904,19744,3739,18947,3381,18448,10384,12576,17805,908,16883,18851,2494,15865,17812,4257,11766,15230,9564,8055,4770,18889,12320,9121,2487,16363,8403,15205,7916,5336,3502,5191,7423,3208,2163};
	  int cores[] = {28,30,2,15,13,29,3,17,12,27,7,6,26,19,3,14,6,5,29,9,12,9,10,16,16,12,24,18,2,32,4,5,25,31,26,4,14,6,1,18,27,23,10,14,1,22,6,3,5,15,12,27,17,16,21,6,16,9,5,24,21,16,24,8,17,30,26,17,31,18,18,20,26,11,15,21,5,18,5};
	  int ecu[] = {90,74,68,8,39,15,87,39,99,78,30,55,81,20,87,3,97,96,2,84,31,31,99,102,18,28,2,15,73,79,49,45,38,93,16,53,55,12,34,11,1,27,24,41,30,39,16,64,100,40,89,88,36,13,61,97,76,80,53,59,2,52,19,2,47,98,22,25,53,54,89,27,90,56,84,52,21,62,90};
	  int ram[] = {220,198,195,222,132,84,191,31,152,67,52,203,170,214,145,140,190,32,120,75,171,126,155,13,167,224,34,47,27,26,188,60,10,210,117,136,93,242,170,147,93,246,175,29,153,223,104,168,25,231,178,90,63,225,141,219,87,148,217,47,116,248,182,96,221,101,8,34,97,116,206,227,176,230,101,164,149,71,144};
	  int costHour[] = {17,12,2,5,17,3,2,17,12,12,17,13,8,15,14,16,13,15,14,11,1,15,15,5,16,10,7,12,2,14,8,9,8,4,5,16,9,10,11,6,2,4,10,11,17,16,3,14,16,7,9,11,5,10,10,13,7,3,9,15,14,4,1,10,3,13,1,10,11,9,1,5,2,11,9,12,3,11,8};
	  int ssdBacked[] = {1,0,1,1,0,0,1,0,1,0,1,0,0,0,1,0,0,1,1,0,0,0,1,0,1,0,1,1,1,1,0,1,0,1,0,0,1,0,0,1,0,0,0,1,1,0,0,1,0,1,0,0,1,1,0,0,0,1,0,1,1,0,1,0,0,0,0,1,0,0,1,1,0,0,0,0,1,1,1};

	  /**
	   * For RealDrupal
	   */  
	  int LineOfCode[] = {9945,551,2849,20827,4497,8618,1292,1097,898,2996,5027,1894,17572,317,2683,284,8419,54270,782,5757,5627,1026,4580,3429,1627,2696,6312,792,2383,13196,2274,1934,13483,11639,50762,3115,998,8483,13390,480,1462,13088,327,3940,13830,1271,3306};
	  double CyclomaticComplexity[] = {0.27,0.16,0.24,0.31,0.17,0.41,0.3,0.29,0.17,0.28,0.29,0.67,0.52,0.19,0.46,0.3,0.26,0.41,0.37,0.23,0.23,0.14,0.51,0.23,0.55,0.44,0.6,0.36,0.44,0.51,0.29,0.63,0.59,0.37,0.26,0.19,0.28,0.56,0.35,0.35,0.23,0.41,1.09,0.47,0.49,0.15,0.39};
	  int TestAssertions[] = {1391,244,677,2138,958,870,94,444,227,287,677,2293,121,0,0,0,1355,1089,538,677,3287,330,347,316,135,1724,106,0,0,456,200,1275,0,0,0,731,0,16,0,0,0,851,6,0,285,7,0};
	  double Installations[] = {5259525,5259525,5259525,5259525,5259525,5259525,5259525,5259525,5259525,5259525,5259525,5259525,747248,747248,747248,747248,5259525,802467,802467,5259525,5259525,5259525,715563,622478,516333,412324,412324,412324,412324,402163,348278,286892,280919,281797,286556,226295,226295,209653,206805,206805,206805,407569,407569,392705,238388,238388,238388};
	  int Developers[] = {94,94,94,94,94,94,94,94,94,94,94,94,75,75,75,75,94,178,178,94,94,94,31,33,7,42,42,42,42,46,21,31,29,7,17,43,43,36,43,43,43,45,45,13,52,52,52};
	  int Changes[] = {4,0,2,16,3,7,2,1,1,3,3,1,32,0,5,1,12,27,0,4,1,2,10,2,7,9,11,4,6,46,14,11,40,90,1,15,0,72,34,2,20,14,1,9,5,4,1};

	  int numFeatures; // how many features	    
	  String problemPath = "./SIPFMs/";
    
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
	  * Read data from files
	 * @throws IOException 
	 * @throws NumberFormatException 
	  */
	 public void readDataFromFiles(String fm) throws NumberFormatException, IOException {
		/**
		 * Read cost
		 */
		cost = new double [numFeatures];
		String path = problemPath  +fm +  ".cost";  
		
		BufferedReader in = new BufferedReader(new FileReader(path));
        String line;
        
        int i = 0;
        while ((line = in.readLine()) != null) {
            line = line.trim();
            
            StringTokenizer st = new StringTokenizer(line, ",");
            while (st.hasMoreTokens()) {
            	 cost[i] = Double.parseDouble(st.nextToken());
            	 i++;
            }   
          
        } // while
        
        in.close(); 
	        
        /**
         * read defects 
         */
        defects = new int [numFeatures];
		path = problemPath  +fm +  ".defects";  
		
		in = new BufferedReader(new FileReader(path));
        
        
        i = 0;
        while ((line = in.readLine()) != null) {
            line = line.trim();
            
            StringTokenizer st = new StringTokenizer(line, ",");
            while (st.hasMoreTokens()) {
            	 defects[i] = Integer.parseInt(st.nextToken());	       
            	 i++;
            }   
          
        } // while
        
        in.close(); 
        
        /**
         * read not_used 
         */
        not_used = new int [numFeatures];
		path = problemPath  +fm +  ".not_used";  
		
		in = new BufferedReader(new FileReader(path));
                
        i = 0;
        while ((line = in.readLine()) != null) {
            line = line.trim();
            
            StringTokenizer st = new StringTokenizer(line, ",");
            while (st.hasMoreTokens()) {
            	 not_used[i] = Integer.parseInt(st.nextToken());	       
            	 i++;
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
	  	      if (fm.equalsIgnoreCase("RealAmazon")) {
	  	    	  strToWrite = "#FEATURE_INDEX costMonth (Min)	cores (Max)	 ecu (Max)	ram (Max)	costHour (Min)	ssdBacked (Max)";
		  	      bw.write(strToWrite);
		  	      bw.newLine();
		  	    
		  	      for(int i = 1;i <= numFeatures;i ++){
					  strToWrite = String.valueOf(i) + " ";  
					  
					  strToWrite = strToWrite + String.valueOf(costMonth[i-1]) + " "; // costMonth 	
					  strToWrite = strToWrite + String.valueOf(cores[i-1]) + " "; // cores
					  strToWrite = strToWrite + String.valueOf(ecu[i-1]) + " "; // ecu
					  strToWrite = strToWrite + String.valueOf(ram[i-1]) + " "; // ram
					  strToWrite = strToWrite + String.valueOf(costHour[i-1]) + " "; // costHour
					  strToWrite = strToWrite + String.valueOf(ssdBacked[i-1]) + " "; // ssdBacked
		  	    	  bw.write(strToWrite);
		  	    	  bw.newLine();
		  	      }   
	  	      } else if (fm.equalsIgnoreCase("RealDrupal")) {
	  	    	  
	  	    	  strToWrite = "#FEATURE_INDEX LineofCode	CyclomaticComplexity	"
	  	    	  		      + "Testcases	Testassertions	Installations	Developers	Changes7.23";
		  	      bw.write(strToWrite);
		  	      bw.newLine();
		  	      System.out.println("LineOfCode" + LineOfCode.length);
		  	      for(int i = 1;i < numFeatures;i ++){
					  strToWrite = String.valueOf(i+1) + " ";  
					  
					  strToWrite = strToWrite + String.valueOf(LineOfCode[i-1]) + " "; // LineOfCode 	
					  strToWrite = strToWrite + String.valueOf(CyclomaticComplexity[i-1]) + " "; // CyclomaticComplexity
					  strToWrite = strToWrite + String.valueOf(TestAssertions[i-1]) + " "; // TestAssertions
					  strToWrite = strToWrite + String.valueOf(Installations[i-1]) + " "; // Installations
					  strToWrite = strToWrite + String.valueOf(Developers[i-1]) + " "; // Developers
					  strToWrite = strToWrite + String.valueOf(Changes[i-1]) + " "; // Changes
		  	    	  bw.write(strToWrite);
		  	    	  bw.newLine();
		  	      }   
	  	    	  
	  	      }else { // for a general case
		  	      strToWrite = "#FEATURE_INDEX COST USED_BEFORE DEFECTS";	  	   
		  	      bw.write(strToWrite);
		  	      bw.newLine();
		  	    
		  	      for(int i = 1;i <= numFeatures;i ++){
		  	    	  strToWrite = String.valueOf(i) + " ";  
		  	    	  
		  	    	  strToWrite = strToWrite + String.valueOf(cost[i-1]) + " "; // cost 	  	    	    	    	
		  	    			  
		  	    	  strToWrite = strToWrite + String.valueOf(not_used[i-1]) + " "; // used before 
		  	    	  
		  	    	  strToWrite = strToWrite + String.valueOf(defects[i-1]) + " "; // defects
		  	    	  
		  	    	  bw.write(strToWrite);
		  	    	  bw.newLine();
		  	      }   
		  	      
	  	      } // else 
 
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
//				"BerkeleyDB",
//				 "Amazon",
//				 "Drupal",
//				 "ERS",
//				 "WebPortal",
//				 "E-shop",
//				 "Random-10000",
				 
//				 "RealAmazon",
				 "RealDrupal",
			};
		 
		 for (int i = 0; i  < fm.length;i++) {
			 generateAugmentForGivenValues ga = new generateAugmentForGivenValues();
			 ga.loadFM(fm[i]);
//			 ga.readDataFromFiles(fm[i]); // for reading from files
			 ga.writeAugments(fm[i]);
			 System.out.println("Write " + fm[i] + " augment to file done!!");
		 }
		
	 }
}
