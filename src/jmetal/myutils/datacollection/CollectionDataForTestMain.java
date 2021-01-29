/*
 * CollectionDataForTestMain.java
 * 
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
package jmetal.myutils.datacollection;

public class CollectionDataForTestMain {

	/**
	 * @param args
	 * @throws Exception 
	 * @throws MatlabConnectionException 
	 * @throws MatlabInvocationException 
	 */
	public static void main(String[] args) throws Exception {

		int runs = 30;
		int t = 6;
		int nbProduts = 100;
		long timeMS = 6000 / 1;
		
		String expPath = "./outputOrder/";
		
		String [] problems= new String[]{	
				
				// -------------6S,30runs------------
	    		"CounterStrikeSimpleFeatureModel",//24
				"SPLSSimuelESPnP", //32
				"DSSample", //41
				"WebPortal",//43    
				"Drupal", //48
				"ElectronicDrum",//52
				"SmartHomev2.2",//60
				"VideoPlayer", // 71
				"Amazon", // 79
				"ModelTransformation", // 88
				"CocheEcologico",//94
				"Printers",//	172	  
				
				
//				// -------------30S,30runs------------
//				"E-shop",//	290		    			
//	  			"toybox", //544
//    			"axTLS", //684    			
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
				
//    			// -------------600S,15 runs------------	
//    			"ecos-icse11",// 1244 
//    			"freebsd-icse11", // 1396 
//    			"Automotive01", //2513 
//    			"SPLOT-3CNF-FM-5000-1000-0,30-SAT-1",// 5000
//    			"2.6.28.6-icse11", //6888
//    			"Automotive02_V3",//18434, YES 
				};
		
		String [] algorithms = new String[]{
				
	    		//-------------------------------R1----------------------------
//	    		"NSR1","GAR1","SamplingDownR1","SAT4JUnpredictableR1",//"Smarch"
	    		
//	    		"NSR1","NSR1JaccardDistance", "NSR1DiceDistance","NSR1HammingDistance",
//				"NSR1RerunForGenWays","Genetic+TwoSAT","RandomizedSAT4J",
				"NSR1Nb=N", "HenardGA", 
	    		//-------------------------------R1 end ----------------------------
	    		
//				 "NSprobSAT",	
//				 "NSprobSATRandom",	
//				 "NSUnpredictable",
//	    		 "GA",
//	    		 "SamplingDown",
//	    		 "SAT4JUnpredictable",
		};
		
		String [] indicators = new String [] {
				"Coverage",
//	    		"MeanFaultRate",
//	    		"RUNTIME",
//	    		"Fitness",
		};
		
		
		(new CollectionDataForTest(runs, expPath, problems,algorithms,indicators,t,nbProduts,timeMS)).execute();
	}
	
}
