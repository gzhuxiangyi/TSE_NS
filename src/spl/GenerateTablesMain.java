/* GenerateTablesMain.java
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
 * Note: This is a free software developed based on the open 
 * source projects PLEDGE <https://github.com/christopherhenard/pledge> 
 * and jMetal<http://jmetal.sourceforge.net>. The copy right of PLEDGE 
 * belongs to  its original author, Christopher Henard, and the copy 
 * right of jMetal belongs to Antonio J. Nebro and Juan J. Durillo. 
 * Nevertheless, this current version can be redistributed and/or 
 * modified under the terms of the GNU  General Public License
 * as published by the Free Software Foundation, either version 3 of 
 * the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful, 
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU  General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 * 
 */
package spl;

import java.io.IOException;

import jmetal.core.Algorithm;
import jmetal.experiments.Experiment;
import jmetal.experiments.Settings;
import jmetal.experiments.util.Friedman;
import jmetal.util.JMException;


public class GenerateTablesMain extends Experiment {

  /**
   * Configures the algorithms in each independent run
   * @param problemName The problem to solve
   * @param problemIndex
   * @throws ClassNotFoundException 
   */
  public void algorithmSettings(String problemName, 
  		                          int problemIndex, 
  		                          Algorithm[] algorithm) throws ClassNotFoundException {
    
  } // algorithmSettings

  /**
   * Main method
   * @param args
   * @throws JMException
   * @throws IOException
   */
  public static void main(String[] args) throws JMException, IOException {
    GenerateTablesMain exp = new GenerateTablesMain();


    exp.experimentName_ = "output";  
//    exp.experimentName_ = "outputOrderParameter";  
    exp.t   = 3; // t-wise, t=0 faults
    exp.nproducts = 100; // the number of products
    exp.timeMS = (long) 6000 / 1; // the time allowed
    
    
    exp.algorithmNameList_ = new String[]{	
    		
    		//-------------------------------R1----------------------------
    		"NS","GA","SamplingDown",
    		//"SAT4JUnpredictableR1","Smarch",
    		
//    		"NSR1","NSR1JaccardDistance", "NSR1DiceDistance","NSR1HammingDistance",
    		
//    		"NSR1P=0.0","NSR1P=0.1","NSR1P=0.2","NSR1P=0.3","NSR1P=0.4","NSR1P=0.5","NSR1P=0.6",
//    		"NSR1P=0.7","NSR1P=0.8","NSR1P=0.9","NSR1P=1.0",
    		
//			"NSR1NbRatio=0.1","NSR1NbRatio=0.2","NSR1NbRatio=0.3","NSR1NbRatio=0.4","NSR1NbRatio=0.5","NSR1NbRatio=0.6",
//			"NSR1NbRatio=0.7","NSR1NbRatio=0.8","NSR1NbRatio=0.9","NSR1NbRatio=1.0",
			
//    		"NSR1RerunForGenWays","Genetic+TwoSAT","RandomizedSAT4J", // Used in different ways of generating configurations
    		
//    		"NSR1Nb=N", "HenardGA", 
    		//-------------------------------R1 end ----------------------------
//    		 "SAT4JUnpredictable",
//    		 "probSATRepair",
//    		 "SAT4JRepair",
//    		 "SMTZ3",
//    		 "SAT4JRepairP0.1",
//    		 "SAT4JRepairP0.5",
//    		 "probSATRepairP0.1",
//    		 "NSProbP0.1",
//    		 "NSP0.0",
//    		 "NSP0.1",//"NSP1.0",
//    		 "GA",
//    		 "SamplingDown","NSprobSAT"
//    		 "ImprovedGA",
    		

//    		 "NSprobSAT",	 // crossover + probSAT
//			 "NSprobSATRandom", // random + probSAT			
//			 "NSUnpredictable", // SAT4J
    		
//    		 "NSprobSATP=0.0", "NSprobSATP=0.1", "NSprobSATP=0.2", "NSprobSATP=0.3", "NSprobSATP=0.4", "NSprobSATP=0.5", 
//    		 "NSprobSATP=0.6","NSprobSATP=0.7", "NSprobSATP=0.8", "NSprobSATP=0.9", "NSprobSATP=1.0", 
    		
//    		"NSprobSATNbr=2","NSprobSATNbr=10","NSprobSATNbr=20","NSprobSATNbr=30","NSprobSATNbr=40","NSprobSATNbr=50",
//    		"NSprobSATNbr=60","NSprobSATNbr=70","NSprobSATNbr=80","NSprobSATNbr=90","NSprobSATNbr=100",
    		
//    		"NSprobSATNscore=0.0","NSprobSATNscore=0.1","NSprobSATNscore=0.2","NSprobSATNscore=0.3","NSprobSATNscore=0.4","NSprobSATNscore=0.5",
//    		"NSprobSATNscore=0.6","NSprobSATNscore=0.7","NSprobSATNscore=0.8","NSprobSATNscore=0.9","NSprobSATNscore=1.0",
    		};
    exp.problemList_ = new String[]{
    		"CounterStrikeSimpleFeatureModel",//24
//			"SPLSSimuelESPnP", //32
//			"DSSample", //41
//			"WebPortal",//43    
//			"Drupal", //48
//			"ElectronicDrum",//52
//			"SmartHomev2.2",//60
//			"VideoPlayer", // 71
//			"Amazon", // 79
//			"ModelTransformation", // 88
//			"CocheEcologico",//94
//			"Printers",//	172	   	
			
//			// -------------30S------------
//			"E-shop",//	290		    			
//  			"toybox", //544
//			"axTLS", //684  
//			"SPLOT-3CNF-FM-1000-200-0,50-SAT-1",
//			"SPLOT-3CNF-FM-1000-200-0,50-SAT-2",
//			"SPLOT-3CNF-FM-1000-200-0,50-SAT-3",
//			"SPLOT-3CNF-FM-1000-200-0,50-SAT-4",
//			"SPLOT-3CNF-FM-1000-200-0,50-SAT-5",
//			"SPLOT-3CNF-FM-1000-200-0,50-SAT-6",
//			"SPLOT-3CNF-FM-1000-200-0,50-SAT-7",
//			"SPLOT-3CNF-FM-1000-200-0,50-SAT-8",
//			"SPLOT-3CNF-FM-1000-200-0,50-SAT-9",
//			"SPLOT-3CNF-FM-1000-200-0,50-SAT-10",
			
//			// -------------600S,15 runs------------	
//			"ecos-icse11",// 1244 
//			"freebsd-icse11", // 1396 
//			"Automotive01", //2513 
//			"SPLOT-3CNF-FM-5000-1000-0,30-SAT-1",// 5000
//			"2.6.28.6-icse11", //6888
//			"Automotive02_V3",//18434, YES 
    		};

    for (int i = 0;i<exp.problemList_.length;i++) {	
    	 exp.problemList_[i] =  exp.problemList_[i] + ".dimacs"; 	
    }
    	
    exp.indicatorList_ = new String[]{
    		"Coverage",
//    		"MeanFaultRate",
//    		"RUNTIME",
//    		"Fitness",
    		};
    
    int numberOfAlgorithms = exp.algorithmNameList_.length;    
      
    exp.experimentBaseDirectory_ = "./" +  exp.experimentName_ ;

    exp.algorithmSettings_ = new Settings[numberOfAlgorithms];

    exp.independentRuns_ = 1;   

    exp.initExperiment();

    // Run the experiments
    int numberOfThreads ;

    exp.generateQualityIndicators() ;

    // Generate latex tables
    exp.generateLatexTables(false) ;    // generate tables without test symbols
//    exp.generateLatexTables(true) ;    // generate tables with test symbols, should perform the  Mann-Whitney U test first
    // Applying Friedman test
    Friedman test = new Friedman(exp);
//    test.executeTest("Coverage");
//    test.executeTest("HV");
//    test.executeTest("GSPREAD");
//    test.executeTest("IGD");
//    test.executeTest("RUNTIME");
  } // main
} // 


