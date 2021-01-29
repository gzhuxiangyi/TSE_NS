/*
 * @author Yi Xiang (xiangyi@scut.edu.cn or gzhuxiang_yi@163.com) 
 * Date: 2020年5月10日
 * Copyright: School of Software Engineering, South China University of Technology
 * All rights reserved
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
 */

package spl.problem.utils;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.StringTokenizer;

/**
 *
 * @author Yi Xiang
 * 
 * This class implements 
 */
public class FeatureIDEFormat2dimacs {
	 String problemPath = "./all_FM/";
	/**
	 * 
	 */
	public FeatureIDEFormat2dimacs() {
		// TODO Auto-generated constructor stub
	}
	
	public void parse(String fm) throws NumberFormatException, IOException, Exception {
		
		  /* Open the read file */
		 String readFile = problemPath + fm +".dimacs";
		 String writeFile= problemPath + fm +"New.dimacs";
		 
		 BufferedReader in = new BufferedReader(new FileReader(readFile)); // read file 		 	 
         String line;
         
         /* Open the write file */
 	      FileOutputStream   fos   = new FileOutputStream(writeFile,false)     ;
 	      OutputStreamWriter osw = new OutputStreamWriter(fos)    ;
 	      BufferedWriter bw      = new BufferedWriter(osw)        ; 	    
 	      String strToWrite;
 	      
 	      
         int n = 0;
         int nbConstraints = 0;
         
         while ((line = in.readLine()) != null) {
             if (line.startsWith("c")) {
            	 StringTokenizer st = new StringTokenizer(line.trim(), " ");
	             st.nextToken();
	             n++;
	             st.nextToken();
	             
	             String featureName = st.nextToken();
	             
	             strToWrite = "c " + n + " " + featureName;             
	             bw.write(strToWrite);
		  	     bw.newLine();
             } else {
            	 if (line.startsWith("p")) {
            		 StringTokenizer st = new StringTokenizer(line.trim(), " ");
            		 st.nextToken(); st.nextToken(); st.nextToken();
            		 strToWrite = "p cnf " + n + " " + st.nextToken();     
            		 bw.write(strToWrite);
    		  	     bw.newLine();
            	 } else {
            		 bw.write(line);
        	  	     bw.newLine();
            		 nbConstraints++;
            	 }           	 
            	 
             }
         }         
        
         System.out.println("number of constraints " + nbConstraints );
         
         in.close();
         bw.close();
	}

	public static void main(String[] args) throws NumberFormatException, IOException, Exception {
		// TODO Auto-generated method stub
		String [] fm = {
    			"2018-01-14T09_51_25-08_00",
    			"2017-01-11T13_56_49+00_00",
    			"2016-01-07T14_11_32+01_00",
    			"2015-01-06T11_04_29-08_00",
    			"2014-01-02T15_48_22-08_00",
    			"2013-11-06T06_39_45+01_00",
		       };

		for (int i = 0; i  < fm.length;i++) {
			FeatureIDEFormat2dimacs transform = new FeatureIDEFormat2dimacs();
			transform.parse(fm[i]);			
			System.out.println("Write " + fm[i] + " augment to file done!!");
		}
	}
}
