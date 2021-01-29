//  FileUtils.java
//

package spl.utils;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.StringTokenizer;

import jmetal.util.Configuration;

/**
 * Utilities methods to used in File operations
 */
public class FileUtils {
    /**
     * Check a dir. If doesn't exit, create one 
     * @param path
     */
	public static void CheckDir(String path) {
		
		File pathDirectory = new File(path);
		    	
		if (pathDirectory.exists()) {
			System.out.println("Path directory exists");
		if (pathDirectory.isDirectory()) {
			System.out.println("Path directory is a directory");
		} else {
			System.out.println("Path directory is not a directory. Deleting file and creating directory");
			}
			pathDirectory.delete();
			new File(path).mkdirs();
		} // if
		else {
			System.out.println("Path directory does NOT exist. Creating");
			new File(path).mkdirs();
		} // else
		
	} // CheckDir
	/**
	 * 
	 * @param file
	 */
	public static void resetFile(String file) {
		File f = new File(file);
		if(f.exists()){			
			System.out.println("File " + file + " exist.");

			if(f.isDirectory()){
				System.out.println("File " + file + " is a directory. Deleting directory.");
				if(f.delete()){
					System.out.println("Directory successfully deleted.");
				}else{
					System.out.println("Error deleting directory.");
				}
			}else{
				System.out.println("File " + file + " is a file. Deleting file.");
				if(f.delete()){
					System.out.println("File succesfully deleted.");
				}else{
					System.out.println("Error deleting file.");
				}
			}			 
		}else{
			System.out.println("File " + file + " does NOT exist.");
		}
	} // resetFile
	/**
	 * Write the content of a matrix into a file 
	 * @param path
	 * 
	 */
	public static void writeMatrix(String path,double [][] matrix,int objectives) {
//		resetFile(path);
		
//	    DecimalFormat df = new DecimalFormat("###.######");
	    
	try {
	      /* Open the file */
	      FileOutputStream fos   = new FileOutputStream(path,true)     ;
	      OutputStreamWriter osw = new OutputStreamWriter(fos)    ;
	      BufferedWriter bw      = new BufferedWriter(osw)        ;
	      
	      int removedPoint = 0;	      
	      int rows = matrix.length;	      	      
	      int cols = objectives;
	      
	      String strToWrite;
	      bw.write("#\n");
	      
	      for(int i = 0;i < rows;i ++){
	    	  // Check whether there are values larger than 1.1
	    	  boolean writeAble = true;
	    	  
	    	  for(int j = 0;j < cols;j++){
	    		  if (matrix[i][j] > 1.1) {
	    			  writeAble = false;
	    			  removedPoint++;
	    			  break;
	    		  }
	    	  }
	    	  
	    	  if (writeAble) {
		    	  strToWrite ="";
		    	  for(int j = 0;j < cols;j++){
		    		  strToWrite = strToWrite + String.valueOf(matrix[i][j]) + "  ";
	//	    		  strToWrite = strToWrite + df.format(matrix[i][j]) + " ";
		    	  }
		    	  bw.write(strToWrite);
		    	  bw.newLine();
	    	  } // if 
	      }     
	      
	      if (removedPoint == rows || rows == 0) {
	    	  System.out.println("All points have been removed....");
	    	  strToWrite ="";
	    	  for(int j = 0;j < cols;j++){
	    		  strToWrite = strToWrite + String.valueOf(1.1) + "  ";
	    	  }
	    	  bw.write(strToWrite);
	    	  bw.newLine();
	      }
//	      bw.newLine();    
	      /* Close the file */
	      bw.close();
	    }catch (IOException e) {
	      Configuration.logger_.severe("Error acceding to the file");
	      e.printStackTrace();
	    }//catch
	
//	System.out.println("File has been written!");		

	}//
	
	/**
	 * Write the content of a matrix into a file 
	 * @param path
	 * 
	 */
	public static void writeMatrixEnd(String path,double [][] matrix, int objectives) {
//		resetFile(path);
	//DecimalFormat df = new DecimalFormat("###.######");
	try {
	      /* Open the file */
	      FileOutputStream fos   = new FileOutputStream(path,true)     ;
	      OutputStreamWriter osw = new OutputStreamWriter(fos)    ;
	      BufferedWriter bw      = new BufferedWriter(osw)        ;
	      int removedPoint = 0;	      
	      int rows = matrix.length;
	      int cols = objectives;
	      String strToWrite;
	      bw.write("#\n");
	      
	      for(int i = 0;i < rows;i ++){
	    	  // Check whether there are values larger than 1.1
	    	  boolean writeAble = true;
	    	  
	    	  for(int j = 0;j < cols;j++){
	    		  if (matrix[i][j] > 1.1) {
	    			  writeAble = false;
	    			  removedPoint++;
	    			  break;
	    		  }
	    	  }
	    	  
	    	  if (writeAble) {
		    	  strToWrite ="";
		    	  for(int j = 0;j < cols;j++){
		    		  strToWrite = strToWrite + String.valueOf(matrix[i][j]) + "  ";
	//	    		  strToWrite = strToWrite + df.format(matrix[i][j]) + " ";
		    	  }
		    	  bw.write(strToWrite);
		    	  bw.newLine();
	    	  } // if 
	      }     
	      
	      if (removedPoint == rows || rows == 0) {
	    	  System.out.println("All points have been removed....");
	    	  strToWrite ="";
	    	  for(int j = 0;j < cols;j++){
	    		  strToWrite = strToWrite + String.valueOf(1.1) + "  ";
	    	  }
	    	  bw.write(strToWrite);
	    	  bw.newLine();
	      }
	      
	      bw.write("#");
	      /* Close the file */
	      bw.close();
	    }catch (IOException e) {
	      Configuration.logger_.severe("Error acceding to the file");
	      e.printStackTrace();
	    }//catch
	
//	System.out.println("File has been written!");		

	}//
	/**
	 * Write the content of a matrix into a file  
	 * @param path
	 * @param append, determine the form 
	 * 
	 */
	public static void writeMatrix(String path,double [][] matrix, boolean append) {
		FileUtils.resetFile(path);
		
	try {
	      /* Open the file */
	      FileOutputStream fos   = new FileOutputStream(path,append)     ;
	      OutputStreamWriter osw = new OutputStreamWriter(fos)    ;
	      BufferedWriter bw      = new BufferedWriter(osw)        ;
	      
	      int rows = matrix.length;
	      int cols = matrix[0].length;	      

	      bw.write("%% Coverage, Similarity-based fitness, NS(Nb=15), NS(Nb=2), NS(Nb=1/4*SampleSize),  NS(Nb=HalfSampleSize), NS(Nb=3/4*SampleSize)");      	
	      bw.newLine();
	      bw.write("data=[");
	      
	      String strToWrite;
	      
	      int done = 0;
	      
	      for(int i = 0;i < rows;i ++){	    	  
	  
	    	  strToWrite ="";
	    	  for(int j = 0;j < cols;j++){
	    		  strToWrite = strToWrite + String.valueOf(matrix[i][j]) + "  ";
	    	  }
	    	  
	    	  bw.write(strToWrite);
	    	  
	    	  done++;
	    	  
	    	  if (done < rows) {
	    		  bw.newLine();
	    	  }	  	    	  
	    	  
	      }     	               

	      bw.write("];"); bw.newLine();
	      
	      bw.write("[R,P] = corrcoef(data)"); bw.newLine();
	      bw.write("mean(data)"); bw.newLine();
	      
	      /* Close the file */
	      bw.close();
	    }catch (IOException e) {
	      Configuration.logger_.severe("Error acceding to the file");
	      e.printStackTrace();
	    }//catch
	
//	System.out.println(path + "File has been written!");		

	}//

	/**
	 * Write the content of a matrix into a file  
	 * @param path
	 * @param append, determine the form 
	 * 
	 */
	public static void writeMatrix2Existing(String path,double [][] matrix, boolean append) {
				
	try {
	      /* Open the file */
	      FileOutputStream fos   = new FileOutputStream(path,append)     ;
	      OutputStreamWriter osw = new OutputStreamWriter(fos)    ;
	      BufferedWriter bw      = new BufferedWriter(osw)        ;
	      
	      int rows = matrix.length;
	      int cols = matrix[0].length;	 
	      
	      bw.newLine();
	      bw.write("%% ---------------Appended data--------------------");      	
	      bw.newLine();
	      bw.write("data(:,2)=[");
	      
	      String strToWrite;
	      
	      int done = 0;
	      
	      for(int i = 0;i < rows;i ++){	    	  
	  
	    	  strToWrite ="";
	    	  for(int j = 0;j < cols;j++){
	    		  strToWrite = strToWrite + String.valueOf(matrix[i][j]) + "  ";
	    	  }
	    	  
	    	  bw.write(strToWrite);
	    	  
	    	  done++;
	    	  
	    	  if (done < rows) {
	    		  bw.newLine();
	    	  }	  	    	  
	    	  
	      }     	               

	      bw.write("];"); bw.newLine();
	      
	      bw.write("[R,P] = corrcoef(data)"); bw.newLine();
	      bw.write("mean(data)"); bw.newLine();
	      
	      /* Close the file */
	      bw.close();
	    }catch (IOException e) {
	      Configuration.logger_.severe("Error acceding to the file");
	      e.printStackTrace();
	    }//catch
	
//	System.out.println(path + "File has been written!");		

	}//
	
	/**
	 * Read the content from a file  
	 * @param path
	 * 
	 */
	public static double [][] readMatrix(String path) {		 
		    try {
		      // Open the file
		      FileInputStream fis   = new FileInputStream(path)     ;
		      InputStreamReader isr = new InputStreamReader(fis)    ;
		      BufferedReader br      = new BufferedReader(isr)      ;
		      
		      List<double []> list = new ArrayList<double []>();
		      int cols = 0;
		      String aux = br.readLine();
		      while (aux!= null) {
		        StringTokenizer st = new StringTokenizer(aux);
		        int i = 0;
		        cols = st.countTokens();
		        double [] vector = new double[st.countTokens()];
		        while (st.hasMoreTokens()) {
		          double value = new Double(st.nextToken());
		          vector[i] = value;
		          i++;
		        }
		        list.add(vector);
		        aux = br.readLine();
		      }
		            
		      br.close();
		      
		      double [][] m = new double[list.size()][cols];
		      for (int i = 0; i < list.size(); i++) {
		        m[i] = list.get(i);
		      }
		      return m;
		      
		    } catch (Exception e) {
		      System.out.println("InputFacilities crashed reading for file: "+path);
		      e.printStackTrace();
		    }
		    return null;		 
	}
	
}
