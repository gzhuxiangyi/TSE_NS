//  Experiment.java
//
//  Authors:
//       Antonio J. Nebro <antonio@lcc.uma.es>
//       Juan J. Durillo <durillo@lcc.uma.es>
//			 Jorgo Rodriguez
//
//  Copyright (c) 2011 Antonio J. Nebro, Juan J. Durillo, Jorge Rodriguez
//
//  This program is free software: you can redistribute it and/or modify
//  it under the terms of the GNU Lesser General Public License as published by
//  the Free Software Foundation, either version 3 of the License, or
//  (at your option) any later version.
//
//  This program is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU Lesser General Public License for more details.
// 
//  You should have received a copy of the GNU Lesser General Public License
//  along with this program.  If not, see <http://www.gnu.org/licenses/>.

package jmetal.util;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Collections;
import java.util.HashMap;
import java.util.Locale;
import java.util.Map;
import java.util.Properties;
import java.util.StringTokenizer;
import java.util.Vector;
import java.util.logging.Level;
import java.util.logging.Logger;

import jmetal.core.Algorithm;
import jmetal.experiments.util.RBoxplot;
import jmetal.experiments.util.RWilcoxon;
import jmetal.experiments.util.RunExperiment;
import jmetal.experiments.util.Statistics;
import jmetal.qualityIndicator.CMetric;
import jmetal.qualityIndicator.Epsilon;
import jmetal.qualityIndicator.GeneralizedSpread;
import jmetal.qualityIndicator.GenerationalDistance;
import jmetal.qualityIndicator.Hypervolume;
import jmetal.qualityIndicator.IGDNS;
import jmetal.qualityIndicator.InvertedGenerationalDistance;
import jmetal.qualityIndicator.InvertedGenerationalDistancePlus;
import jmetal.qualityIndicator.PD;
import jmetal.qualityIndicator.Spread;
import jmetal.qualityIndicator.util.MetricsUtil;
import jmetal.util.Configuration;
import jmetal.util.JMException;
import jmetal.util.NonDominatedSolutionList;
/**
 * Abstract class representing jMetal experiments
 */
public abstract class Experiment {

	public String experimentName_;
	public String[] algorithmNameList_; // List of the names of the algorithms to be executed
	public String[] problemList_; // List of problems to be solved
	public String[] paretoFrontFile_; // List of the files containing the pareto fronts
	// corresponding to the problems in problemList_
	public String[] indicatorList_; // List of the quality indicators to be applied
	public String experimentBaseDirectory_; // Directory to store the results
	public String latexDirectory_; // Directory to store the latex files  
	public String paretoFrontDirectory_; // Directory containing the Pareto front files
	public String outputParetoFrontFile_; // Name of the file containing the output
	public String outputRuntimeFile_; // Name of the file containing the runtime
	
	// Pareto front
	public String outputParetoSetFile_; // Name of the file containing the output
	// Pareto set
	public int independentRuns_; // Number of independent runs per algorithm
	public Settings[] algorithmSettings_; // Paremeter experiments.settings of each algorithm
	//Algorithm[] algorithm_; // jMetal algorithms to be executed
	HashMap<String, Object> map_; // Map used to send experiment parameters to threads
	public HashMap<String, Boolean> indicatorMinimize_; // To indicate whether an indicator
	// is to be minimized. Hard-coded
	// in the constructor

	public Properties [] problemsSettings_ ;

	//Inicio modificación ReferenceFronts
	public String[] frontPath_; // Path of each reference front file
	// Fin modificación ReferenceFronts
	public String[][] problemPath_;
	
	// Inicio modificación planificación Threads
	public boolean finished_;	// Flag to indicate when the experiment has ended
	public static int algorithmIndex; // Index of the next algorithm to run
	public static int problemIndex; // Index of the next problem to solve
	public static int irunIndex; // Counter of the independent runs
	// Fin modificación planificación Threads
    public int noOfObjectives_; // The number of objectives this experiment considers
    public int noOfVariables_; // The number of variables this experiment considers
    public int noOfFEs_; // The number of FEs this experiment considers
	/**
	 * Constructor
	 *
	 * Contains default experiments.settings
	 */
	public Experiment() {
		experimentName_ = "noName";

		problemsSettings_ = null ;

		map_ = new HashMap<String, Object>();

		algorithmNameList_ = null;
		problemList_ = null;
		paretoFrontFile_ = null;
		indicatorList_ = null;

		// Inicio modificación ReferenceFronts
		frontPath_ = null;
		// Fin modificación ReferenceFronts

		experimentBaseDirectory_ = "";
		paretoFrontDirectory_ = "";
		latexDirectory_ = "latex";    

		outputParetoFrontFile_ = "FUN";
		outputParetoSetFile_ = "VAR";
		outputRuntimeFile_ = "RUNTIME";

		algorithmSettings_ = null;
		//algorithm_ = null;

		independentRuns_ = 0;

		indicatorMinimize_ = new HashMap<String, Boolean>();
		indicatorMinimize_.put("HV", false);
		indicatorMinimize_.put("HV2", false);
		indicatorMinimize_.put("HypE Hypervolume", false);
		indicatorMinimize_.put("DCI", false);
		indicatorMinimize_.put("PD", false);
		indicatorMinimize_.put("EPSILON", true);
		indicatorMinimize_.put("SPREAD", true);
		indicatorMinimize_.put("GSPREAD", true);
		indicatorMinimize_.put("GD", true);
		indicatorMinimize_.put("GenerationDistance", true);
		indicatorMinimize_.put("IGD", true);
		indicatorMinimize_.put("IGD+", true);
		indicatorMinimize_.put("IGDNS", true);
		indicatorMinimize_.put("UD", true);
		indicatorMinimize_.put("FUN", true);
		indicatorMinimize_.put("RUNTIME", true);
		indicatorMinimize_.put("FS", false);
		indicatorMinimize_.put("CMetric", false);
		
		noOfObjectives_    =  2; // Two objectives by defaults
		noOfVariables_ = noOfObjectives_; // The number of variables this experiment considers
		noOfFEs_ = 100; // The number of FEs this experiment considers
		
		// Inicio modificación planificación Threads
		problemIndex = 0;
		algorithmIndex = 0;
		irunIndex = 0;
		// Fin modificacion planificación Threads
	} // Constructor

	
	/**
	 * Runs the experiment
	 */
	public void runExperiment(int numberOfThreads) throws JMException, IOException {

		//initExperiment();
		//SolutionSet[] resultFront = new SolutionSet[algorithmNameList_.length];

		// Inicio modificación planificación Threads
		System.out.println("Experiment: Name: " + experimentName_);
		System.out.println("Experiment: creating " + numberOfThreads + " threads");
		System.out.println("Experiment: Number of algorithms: " + algorithmNameList_.length) ;
		System.out.println("Experiment: Number of problems: " + problemList_.length);
		System.out.println("Experiment: runs: " + independentRuns_) ;		
		System.out.println("Experiment: Experiment directory: " + experimentBaseDirectory_);

		// Fin modificación planificación Threads

		Thread[] p = new RunExperiment[numberOfThreads];
		for (int i = 0; i < numberOfThreads; i++) {
			//p[i] = new Experiment(map_, i, numberOfThreads, problemList_.length);
			p[i] = new RunExperiment(this, map_, i, numberOfThreads, problemList_.length);
			p[i].start();
		}

		try {
			for (int i = 0; i < numberOfThreads; i++) {
				p[i].join();
			}
		} catch (InterruptedException ex) {
			Logger.getLogger(Experiment.class.getName()).log(Level.SEVERE, null, ex);
		}

		// Inicio modificación ReferenceFronts
		//generateQualityIndicators();
		// Fin modificación ReferenceFronts
	}

	/**
	 * Runs the experiment
	 */
	public void runExperiment() throws JMException, IOException {
		runExperiment(1);
	} // runExperiment

	public void initExperiment(){
		// Step 1: check experiment base directory
		checkExperimentDirectory();

		map_.put("experimentName", experimentName_);
		map_.put("experimentDirectory", experimentBaseDirectory_);
		map_.put("algorithmNameList", algorithmNameList_);
		map_.put("problemList", problemList_);
		map_.put("indicatorList", indicatorList_);
		map_.put("paretoFrontDirectory", paretoFrontDirectory_);
		map_.put("paretoFrontFile", paretoFrontFile_);
		map_.put("independentRuns", independentRuns_);
		map_.put("outputParetoFrontFile", outputParetoFrontFile_);
		map_.put("outputParetoSetFile", outputParetoSetFile_);
		map_.put("outputRuntimeFile", outputRuntimeFile_);
		map_.put("problemsSettings", problemsSettings_);
		map_.put("noOfObjectives", noOfObjectives_);
		
		// Inicio modificación ReferenceFronts
		frontPath_ = new String[problemList_.length];
		map_.put("frontPath",frontPath_);
		// Fin modificación ReferenceFrons
	}

	
	public void runCompleteExperiment() throws JMException, IOException{
		runCompleteExperiment(1);
	}
	
	public void runCompleteExperiment(int numberOfThreads) throws JMException, IOException{
		this.initExperiment();
		this.runExperiment(numberOfThreads);
		this.generateQualityIndicators();
	}
	
	private void checkExperimentDirectory() {
		File experimentDirectory;

		experimentDirectory = new File(experimentBaseDirectory_);
		if (experimentDirectory.exists()) {
			System.out.println("Experiment directory exists");
			if (experimentDirectory.isDirectory()) {
				System.out.println("Experiment directory is a directory");
			} else {
				System.out.println("Experiment directory is not a directory. Deleting file and creating directory");
			}
			experimentDirectory.delete();
			new File(experimentBaseDirectory_).mkdirs();
		} // if
		else {
			System.out.println("Experiment directory does NOT exist. Creating");
			new File(experimentBaseDirectory_).mkdirs();
		} // else
	} // checkDirectories

	/**
	 * Especifies the experiments.settings of each algorith. This method is checked in each
	 * experiment run
	 * @param problem Problem to solve
	 * @param problemId Index of the problem in problemList_
	 * @param algorithm Array containing the algorithms to execute
	 * @throws ClassNotFoundException 
	 */
	public abstract void algorithmSettings(String problemName, int problemId, Algorithm[] algorithm) throws ClassNotFoundException;

	public static void main(String[] args) throws JMException, IOException {
	}

    //Inicio modificación ReferenceFronts

	/**
	 * Checks if exist paretoFront files
	 */
	private void checkParetoFronts(){	
		Logger      logger_ ;
		if(paretoFrontDirectory_.equals("") || paretoFrontDirectory_ == null){
			logger_      = Configuration.logger_ ;
			logger_.info("---------------------------OK------------------------");
			System.out.print("-----------------------------Ok---------------------");
			generateReferenceFronts();
		}else{
			for(int i = 0; i < problemList_.length; i ++){
				if(paretoFrontFile_[i]==null || paretoFrontFile_[i].equals("")){
					paretoFrontFile_[i] = "";
					generateReferenceFronts(i);
				}else{
					String filePath = paretoFrontDirectory_ + "/" + paretoFrontFile_[i];					
					File f = new File(filePath);							
					if(!f.exists()){
						paretoFrontFile_[i] = "";
						generateReferenceFronts(i);
					}else{
						frontPath_[i] = paretoFrontDirectory_ + "/" + paretoFrontFile_[i];
					} // if
				} // if
			} // for
		} // if
	} // checkParetoFronts

	/**
	 * Generate the Quality Indicators
	 */
	public void generateQualityIndicators() {

		checkParetoFronts();

		if (indicatorList_.length == 1 && indicatorList_[0].equals("CMetric")) { // Calculate CM separately. 

			for (int algorithmIndex=0; algorithmIndex<algorithmNameList_.length; algorithmIndex++) {

				String algorithmDirectory;
				algorithmDirectory = experimentBaseDirectory_ + "/data/" + algorithmNameList_[algorithmIndex] + "/";

				for (int problemIndex = 0; problemIndex < problemList_.length; problemIndex++) { // Each time 

					String problemDirectory = algorithmDirectory + problemList_[problemIndex];					
					
					// The following code is to show how to compare an algorithm's performance on two different problems					
					String comparingProblemDirectory;
					
					if (problemIndex % 2 == 0) { 
						comparingProblemDirectory = algorithmDirectory + problemList_[problemIndex+1];
					} else {
						comparingProblemDirectory = algorithmDirectory + problemList_[problemIndex-1];
					}

                    for (String anIndicatorList_ : indicatorList_) {
                        System.out.println("Experiment - Quality indicator: " + anIndicatorList_);

                        resetFile(problemDirectory + "/" + anIndicatorList_);

                        for (int numRun = 0; numRun < independentRuns_; numRun++) {

                            String outputParetoFrontFilePath;
                            outputParetoFrontFilePath = problemDirectory + "/FUN." + numRun;
                            String solutionFrontFile = outputParetoFrontFilePath;
                            String comparingSolutionFrontFile = comparingProblemDirectory + "/FUN." + numRun; 
                            
                            String qualityIndicatorFile = problemDirectory;
                            double value = 0;     
                            
                            if (anIndicatorList_.equals("CMetric")) {
                            	CMetric indicators = new CMetric();
                                double[][] solutionFront = indicators.utils_.readFront(solutionFrontFile);
                               
                                double[][] comparingSolutionFront =  indicators.utils_.readFront(comparingSolutionFrontFile);                                

                                value = indicators.CMetric(solutionFront, comparingSolutionFront, noOfObjectives_);

                                qualityIndicatorFile = qualityIndicatorFile + "/CMetric";
                            }
                                      
                            
                            if (!qualityIndicatorFile.equals(problemDirectory)) {
                                FileWriter os;
                                try {
                                    os = new FileWriter(qualityIndicatorFile, true);
                                    os.write("" + value + "\n");
                                    os.close();
                                } catch (IOException ex) {
                                    Logger.getLogger(Experiment.class.getName()).log(Level.SEVERE, null, ex);
                                }
                            } // if
                        } // for
                    } // for
				} // for
			} // for
			return;
		} // if
		
		if (indicatorList_.length > 0) {

			for (int algorithmIndex=0; algorithmIndex<algorithmNameList_.length; algorithmIndex++) {

				String algorithmDirectory;
				algorithmDirectory = experimentBaseDirectory_ + "/data/" + algorithmNameList_[algorithmIndex] + "/";

				for (int problemIndex=0; problemIndex<problemList_.length; problemIndex++) {

					String problemDirectory = algorithmDirectory + problemList_[problemIndex];
					String paretoFrontPath = frontPath_[problemIndex];

                    for (String anIndicatorList_ : indicatorList_) {
                        System.out.println("Experiment - Quality indicator: " + anIndicatorList_);

                        resetFile(problemDirectory + "/" + anIndicatorList_);

                        for (int numRun = 0; numRun < independentRuns_; numRun++) {

                            String outputParetoFrontFilePath;
                            outputParetoFrontFilePath = problemDirectory + "/FUN." + numRun;
                            String solutionFrontFile = outputParetoFrontFilePath;
                            String qualityIndicatorFile = problemDirectory;
                            double value = 0;

                            if (anIndicatorList_.equals("HV")) {

                                Hypervolume indicators = new Hypervolume();
                                double[][] solutionFront =
                                        indicators.utils_.readFront(solutionFrontFile);
                                double[][] trueFront =
                                        indicators.utils_.readFront(paretoFrontPath);
                                
                                value = indicators.hypervolume(solutionFront, trueFront, trueFront[0].length);

                                qualityIndicatorFile = qualityIndicatorFile + "/HV";

                            }
                            
                            if (anIndicatorList_.equals("GSPREAD")) {
                            	GeneralizedSpread indicators = new GeneralizedSpread();
                                double[][] solutionFront =
                                        indicators.utils_.readFront(solutionFrontFile);
                                double[][] trueFront =
                                        indicators.utils_.readFront(paretoFrontPath);
                                value = indicators.generalizedSpread(solutionFront, trueFront, trueFront[0].length);

                                qualityIndicatorFile = qualityIndicatorFile + "/GSPREAD";
                            }
                            
                            if (anIndicatorList_.equals("SPREAD")) {
                            	Spread indicators = new Spread();
                                double[][] solutionFront =
                                        indicators.utils_.readFront(solutionFrontFile);
                                double[][] trueFront =
                                        indicators.utils_.readFront(paretoFrontPath);
                                value = indicators.spread(solutionFront, trueFront, trueFront[0].length);

                                qualityIndicatorFile = qualityIndicatorFile + "/SPREAD";
                            }
                            
                            if (anIndicatorList_.equals("IGD")) {
                                InvertedGenerationalDistance indicators = new InvertedGenerationalDistance();
                                double[][] solutionFront =
                                        indicators.utils_.readFront(solutionFrontFile);
                               
                                double[][] trueFront =
                                        indicators.utils_.readFront(paretoFrontPath);                                

                                value = indicators.invertedGenerationalDistance(solutionFront, trueFront, trueFront[0].length);

                                qualityIndicatorFile = qualityIndicatorFile + "/IGD";
                            }
                            
                            if (anIndicatorList_.equals("IGD+")) {
                                InvertedGenerationalDistancePlus indicators = new InvertedGenerationalDistancePlus();
                                double[][] solutionFront = indicators.utils_.readFront(solutionFrontFile);
                               
                                double[][] trueFront =  indicators.utils_.readFront(paretoFrontPath);                                

                                value = indicators.invertedGenerationalDistancePlus(solutionFront, trueFront, trueFront[0].length);

                                qualityIndicatorFile = qualityIndicatorFile + "/IGD+";
                            }                                                      
                            
                            if (anIndicatorList_.equals("IGDNS")) {
                                IGDNS indicators = new IGDNS();
                                double[][] solutionFront =
                                        indicators.utils_.readFront(solutionFrontFile);
                               
                                double[][] trueFront =
                                        indicators.utils_.readFront(paretoFrontPath);                                

                                value = indicators.IGDNS(solutionFront, trueFront, trueFront[0].length);

                                qualityIndicatorFile = qualityIndicatorFile + "/IGDNS";
                            }
                            
                            if (anIndicatorList_.equals("PD")) {
                                PD indicators = new PD();
                                double[][] solutionFront =
                                        indicators.utils_.readFront(solutionFrontFile);                                               
                                double[][] trueFront =
                                        indicators.utils_.readFront(paretoFrontPath);
                                   // Method 1: PF�ı߽�ֵ��֪ʱʹ��consider convergence
                                value = indicators.PD(solutionFront, solutionFront[0].length, problemList_[problemIndex]); 
                                  // Method 2: �����Ƕ����ԣ�����׼ȷ
//                                value = indicators.PD(solutionFront, solutionFront[0].length); 
                                // Method 3: ��ݽ���PF����PD,���PF�ı߽��޳�㡣����DTLZ5-7��WFG3�ȣ��Լ�ʵ��Ӧ������
//                                value = indicators.PD(solutionFront, trueFront, solutionFront[0].length); 
                              
                                qualityIndicatorFile = qualityIndicatorFile + "/PD";
                            }
                            
                            if (anIndicatorList_.equals("UD")) {
                                PD indicators = new PD();
                                double[][] solutionFront =
                                        indicators.utils_.readFront(solutionFrontFile);     

                                value = indicators.UD(solutionFront, solutionFront[0].length);

                                qualityIndicatorFile = qualityIndicatorFile + "/UD";
                            }
                            if (anIndicatorList_.equals("GD")) {
                                GenerationalDistance indicators = new GenerationalDistance();
                                double[][] solutionFront =
                                        indicators.utils_.readFront(solutionFrontFile);
                                double[][] trueFront =
                                        indicators.utils_.readFront(paretoFrontPath);
                                value = indicators.generationalDistance(solutionFront, trueFront, trueFront[0].length);

                                qualityIndicatorFile = qualityIndicatorFile + "/GD";
                            }
                            
                            if (anIndicatorList_.equals("EPSILON")) {
                                Epsilon indicators = new Epsilon();
                                double[][] solutionFront = indicators.utils_.readFront(solutionFrontFile);
                                double[][] trueFront =  indicators.utils_.readFront(paretoFrontPath);
                                value = indicators.epsilon(solutionFront, trueFront, trueFront[0].length);

                                qualityIndicatorFile = qualityIndicatorFile + "/EPSILON";
                            }
                            
                            // The objective value is the indicator, often used in sigle-objecitve problems.
                            if (anIndicatorList_.equals("FUN")) {
                            	MetricsUtil utils = new MetricsUtil(); 
                                double[][] solutionFront =
                                        utils.readFront(solutionFrontFile);
                               
                                value = solutionFront[0][0];

                                qualityIndicatorFile = qualityIndicatorFile + "/FUN";

                            }
                            // Evaluate algorithms in terms of runtime
                            if (anIndicatorList_.equals("RUNTIME")) {
                            	MetricsUtil utils = new MetricsUtil(); 
                            	String runtimeFile = problemDirectory + "/RUNTIME." + numRun;
                                double[][] runtime =
                                       utils.readFront(runtimeFile);
                              
                               value = runtime[0][0];

                               qualityIndicatorFile = qualityIndicatorFile + "/RUNTIME";

                           }

                            if (anIndicatorList_.equals("FS")) {
                            	MetricsUtil utils = new MetricsUtil(); 
                            	String fsFile = problemDirectory + "/FS." + numRun;
                                double[][] fs = utils.readFront(fsFile);
                              
                               value = fs[0][0];

                               qualityIndicatorFile = qualityIndicatorFile + "/FS";

                           }
                            
                            if (!qualityIndicatorFile.equals(problemDirectory)) {
                                FileWriter os;
                                try {
                                    os = new FileWriter(qualityIndicatorFile, true);
                                    os.write("" + value + "\n");
                                    os.close();
                                } catch (IOException ex) {
                                    Logger.getLogger(Experiment.class.getName()).log(Level.SEVERE, null, ex);
                                }
                            } // if
                        } // for
                    } // for
				} // for
			} // for
		} // if
	}

	/**
	 * 
	 * @param file
	 */
	public void resetFile(String file) {
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
	 * 
	 * @param problemIndex
	 */
	public void generateReferenceFronts(int problemIndex) {

		File rfDirectory;
		String referenceFrontDirectory = experimentBaseDirectory_ + "/referenceFronts";

		rfDirectory = new File(referenceFrontDirectory);

		if(!rfDirectory.exists()) { 													// Si no existe el directorio
			boolean result = new File(referenceFrontDirectory).mkdirs();				// Lo creamos
			System.out.println("Creating " + referenceFrontDirectory);
		}

		frontPath_[problemIndex] = referenceFrontDirectory + "/" + problemList_[problemIndex] + ".M" + noOfObjectives_ + ".rf";

		MetricsUtil metricsUtils = new MetricsUtil();
		NonDominatedSolutionList solutionSet = new NonDominatedSolutionList();
        for (String anAlgorithmNameList_ : algorithmNameList_) {

            String problemDirectory = experimentBaseDirectory_ + "/data/" + anAlgorithmNameList_ +
                    "/" + problemList_[problemIndex];

            for (int numRun = 0; numRun < independentRuns_; numRun++) {

                String outputParetoFrontFilePath;
                outputParetoFrontFilePath = problemDirectory + "/FUN." + numRun;
                String solutionFrontFile = outputParetoFrontFilePath;

                String solutionVariableFile = problemDirectory + "/VAR." + numRun;
                
//                metricsUtils.readNonDominatedSolutionSet(solutionFrontFile, solutionVariableFile, solutionSet); // This is the original code
                
                metricsUtils.readNonDominatedSolutionSet(solutionFrontFile,solutionSet); // This is our code
            } // for
        } // for
		solutionSet.printObjectivesToFile(frontPath_[problemIndex]);	
		
//		String solutionVariablePath = referenceFrontDirectory + "/" + problemList_[problemIndex] + ".M" + noOfObjectives_ +".var";
//		solutionSet.printFeasibleVAR(solutionVariablePath);
		System.out.println("The number of nondominated solutions of " + problemList_[problemIndex] + " is "+ solutionSet.size());
	} // generateReferenceFronts


	/**
	 * 
	 */
	public void generateReferenceFronts() {

		for (int problemIndex=0; problemIndex<problemList_.length; problemIndex++) {	// Por cada problema, generamos el frente de referencia
			
			this.generateReferenceFronts(problemIndex);

		} // for
	} // generateReferenceFronts

	// Fin modificación ReferenceFronts

	public void generateLatexTables(boolean ifTest) throws FileNotFoundException, IOException {
		latexDirectory_ = experimentBaseDirectory_ + "/" + latexDirectory_;
		System.out.println("latex directory: " + latexDirectory_);

		Vector[][][] data = new Vector[indicatorList_.length][][];
		for (int indicator = 0; indicator < indicatorList_.length; indicator++) {
			// A data vector per problem
			data[indicator] = new Vector[problemList_.length][];

			for (int problem = 0; problem < problemList_.length; problem++) {
				data[indicator][problem] = new Vector[algorithmNameList_.length];

				for (int algorithm = 0; algorithm < algorithmNameList_.length; algorithm++) {
					data[indicator][problem][algorithm] = new Vector();

					String directory = experimentBaseDirectory_;
					directory += "/data/";
					directory += "/" + algorithmNameList_[algorithm];
					directory += "/" + problemList_[problem];
					directory += "/" + indicatorList_[indicator];				
					
					if (indicatorList_[indicator].equalsIgnoreCase("HypE Hypervolume")) {
						directory += ".txt";			
					}
					// Read values from data files
					FileInputStream fis = new FileInputStream(directory);
					InputStreamReader isr = new InputStreamReader(fis);
					BufferedReader br = new BufferedReader(isr);
					//System.out.println(directory);
					String aux = br.readLine();
					while (aux != null && !"".equalsIgnoreCase(aux)) {						
						data[indicator][problem][algorithm].add(Double.parseDouble(aux));
						//System.out.println(Double.parseDouble(aux));
						aux = br.readLine();
					} // while
				} // for
			} // for
		} // for

		double[][][] mean;
		double[][][] median;
		double[][][] stdDeviation;
		double[][][] iqr;
		double[][][] max;
		double[][][] min;
		int[][][] numberOfValues;

		Map<String, Double> statValues = new HashMap<String, Double>();

		statValues.put("mean", 0.0);
		statValues.put("median", 0.0);
		statValues.put("stdDeviation", 0.0);
		statValues.put("iqr", 0.0);
		statValues.put("max", 0.0);
		statValues.put("min", 0.0);

		mean = new double[indicatorList_.length][][];
		median = new double[indicatorList_.length][][];
		stdDeviation = new double[indicatorList_.length][][];
		iqr = new double[indicatorList_.length][][];
		min = new double[indicatorList_.length][][];
		max = new double[indicatorList_.length][][];
		numberOfValues = new int[indicatorList_.length][][];

		for (int indicator = 0; indicator < indicatorList_.length; indicator++) {
			// A data vector per problem
			mean[indicator] = new double[problemList_.length][];
			median[indicator] = new double[problemList_.length][];
			stdDeviation[indicator] = new double[problemList_.length][];
			iqr[indicator] = new double[problemList_.length][];
			min[indicator] = new double[problemList_.length][];
			max[indicator] = new double[problemList_.length][];
			numberOfValues[indicator] = new int[problemList_.length][];

			for (int problem = 0; problem < problemList_.length; problem++) {
				mean[indicator][problem] = new double[algorithmNameList_.length];
				median[indicator][problem] = new double[algorithmNameList_.length];
				stdDeviation[indicator][problem] = new double[algorithmNameList_.length];
				iqr[indicator][problem] = new double[algorithmNameList_.length];
				min[indicator][problem] = new double[algorithmNameList_.length];
				max[indicator][problem] = new double[algorithmNameList_.length];
				numberOfValues[indicator][problem] = new int[algorithmNameList_.length];

				for (int algorithm = 0; algorithm < algorithmNameList_.length; algorithm++) {
					Collections.sort(data[indicator][problem][algorithm]);

					String directory = experimentBaseDirectory_;
					directory += "/" + algorithmNameList_[algorithm];
					directory += "/" + problemList_[problem];
					directory += "/" + indicatorList_[indicator];

					//System.out.println("----" + directory + "-----");
					//calculateStatistics(data[indicator][problem][algorithm], meanV, medianV, minV, maxV, stdDeviationV, iqrV) ;
					calculateStatistics(data[indicator][problem][algorithm], statValues);
					/*
          System.out.println("Mean: " + statValues.get("mean"));
          System.out.println("Median : " + statValues.get("median"));
          System.out.println("Std : " + statValues.get("stdDeviation"));
          System.out.println("IQR : " + statValues.get("iqr"));
          System.out.println("Min : " + statValues.get("min"));
          System.out.println("Max : " + statValues.get("max"));
          System.out.println("N_values: " + data[indicator][problem][algorithm].size()) ;
					 */
					mean[indicator][problem][algorithm] = statValues.get("mean");
					median[indicator][problem][algorithm] = statValues.get("median");
					stdDeviation[indicator][problem][algorithm] = statValues.get("stdDeviation");
					iqr[indicator][problem][algorithm] = statValues.get("iqr");
					min[indicator][problem][algorithm] = statValues.get("min");
					max[indicator][problem][algorithm] = statValues.get("max");
					numberOfValues[indicator][problem][algorithm] = data[indicator][problem][algorithm].size();
				}
			}
		}

		/**
		 * Get statistical test results from files in latex directory  ---------------------begin
		 */
		String [][][] testSymbols = new String[indicatorList_.length][][];
		if (ifTest == true) {
			//String [][][] testSymbols = new String[indicatorList_.length][][];
			
			
			for (int indicator = 0; indicator < indicatorList_.length; indicator++) {
				// A data vector per problem
				testSymbols[indicator] = new String[problemList_.length][];
				
				// Read data from files
				String symbolFile = experimentBaseDirectory_ + "/DataForTest/" + indicatorList_[indicator] + "/" + indicatorList_[indicator] + ".tr";
				
				// Read values from data files
				FileInputStream fis = new FileInputStream(symbolFile);
				InputStreamReader isr = new InputStreamReader(fis);
				BufferedReader br = new BufferedReader(isr);
		
				String aux = br.readLine();			
				
				for (int problem = 0; problem < problemList_.length; problem++) {
					testSymbols[indicator][problem] = new String[algorithmNameList_.length];
					
					StringTokenizer st = new StringTokenizer(aux);			
					
					for (int algorithm = 0; algorithm < algorithmNameList_.length; algorithm++) {
						testSymbols[indicator][problem][algorithm] = st.nextToken();	
					}
					
					aux = br.readLine();				
				}
				
				br.close();
			} // for indicator		
	    } // if ifTest == true
		//----------------------------------------------------------------------------end
		
		File latexOutput;
		latexOutput = new File(latexDirectory_);
		if (!latexOutput.exists()) {
			boolean result = new File(latexDirectory_).mkdirs();
			System.out.println("Creating " + latexDirectory_ + " directory");
		}
		//System.out.println("Experiment name: " + experimentName_);
		String latexFile = latexDirectory_ + "/" + experimentName_ + ".tex";
		printHeaderLatexCommands(latexFile);		
		
		for (int i = 0; i < indicatorList_.length; i++) {
			String fileNameforTest = latexDirectory_ + "/" + experimentName_ + "." ;
			
			// Print mean and std deviation
//			printMeanStdDev(latexFile, i, mean, stdDeviation);
			// Print mean only
//			printMeanStdDev(latexFile, i, mean);//
			
			// Print mean, std deviation and testSymbols
//			if (ifTest == true)
//				printMeanStdSymbols(latexFile, i, mean, stdDeviation,testSymbols);	
//			else 
//				printMeanStdDev(latexFile, i, mean, stdDeviation);	
										
//			String meanforTest = fileNameforTest + indicatorList_[i]+".mean.csv";
//			printMeanforTest(meanforTest, i, mean);

			
			/**
			 * Print median 
			 */
//			printMedianIQR(latexFile, i, median, iqr);			
//			printMedian(latexFile, i, median);
//			printMedianSymbols(latexFile, i, median,testSymbols);
			
			// Print median,iqr and testSymbols			
//			if (ifTest == true)
//				printMedianSymbols(latexFile, i, median,testSymbols);
//			else 
//				printMedian(latexFile, i, median);
			
			if (ifTest == true)
				printMeanSymbols(latexFile, i, median,testSymbols);
			else 
				printMeanStdDev(latexFile, i, median);//
			
//			printMedianIQRSymbols(latexFile, i, median, iqr,testSymbols);	
			
			String medianforTest = fileNameforTest + indicatorList_[i]+".median.csv";
			printMeanforTest(medianforTest, i, median);			
			
		} // for
		printEndLatexCommands(latexFile);
	} // generateLatexTables

	/**
	 * Calculates statistical values from a vector of Double objects
	 * @param vector
	 * @param values
	 */
	void calculateStatistics(Vector vector,
			Map<String, Double> values) {

		if (vector.size() > 0) {
			double sum, minimum, maximum, sqsum, min, max, median, mean, iqr, stdDeviation;

			sqsum = 0.0;
			sum = 0.0;
			min = 1E300;
			max = -1E300;
			median = 0;

			for (int i = 0; i < vector.size(); i++) {
				double val = (Double) vector.elementAt(i);

				sqsum += val * val;
				sum += val;
				if (val < min) {
					min = val;
				}
				if (val > max) {
					max = val;
				} // if
			} // for

			// Mean
			mean = sum / vector.size();

			// Standard deviation
			if (sqsum / vector.size() - mean * mean < 0.0) {
				stdDeviation = 0.0;
			} else {
				stdDeviation = Math.sqrt(sqsum / vector.size() - mean * mean);
			} // if

			// Median
			if (vector.size() % 2 != 0) {
				median = (Double) vector.elementAt(vector.size() / 2);
			} else {
				median = ((Double) vector.elementAt(vector.size() / 2 - 1) +
						(Double) vector.elementAt(vector.size() / 2)) / 2.0;
			} // if

			values.put("mean", mean);
			values.put("median", Statistics.calculateMedian(vector, 0, vector.size() - 1));
			values.put("iqr", Statistics.calculateIQR(vector));
			values.put("stdDeviation", stdDeviation);
			values.put("min", (Double) min);
			values.put("max", (Double) max);
		} // if
		else {
			values.put("mean", Double.NaN);
			values.put("median", Double.NaN);
			values.put("iqr", Double.NaN);
			values.put("stdDeviation", Double.NaN);
			values.put("min", Double.NaN);
			values.put("max", Double.NaN);
		} // else
	} // calculateStatistics


	void printHeaderLatexCommands(String fileName) throws IOException {
		FileWriter os = new FileWriter(fileName, false);
		os.write("\\documentclass[a3paper]{article}" + "\n");
		os.write("\\title{" + experimentName_ + "}" + "\n");
		os.write("\\usepackage{colortbl}" + "\n");
		os.write("\\usepackage{geometry}" + "\n");		
		os.write("\\usepackage[table*]{xcolor}" + "\n");
		os.write("\\xdefinecolor{gray95}{gray}{0.65}" + "\n");
		os.write("\\xdefinecolor{gray25}{gray}{0.8}" + "\n");
		os.write("\\author{}" + "\n");
		os.write("\\begin{document}" + "\n");
//		os.write("geometry{left=2.5cm,right=2.5cm,top=2.5cm,bottom=2.5cm}");
		os.write("\\maketitle" + "\n");
		os.write("\\section{Tables}" + "\n");

		os.close();
	}

	void printEndLatexCommands(String fileName) throws IOException {
		FileWriter os = new FileWriter(fileName, true);
		os.write("\\end{document}" + "\n");
		os.close();
	} // printEndLatexCommands

	void printMeanStdDev(String fileName, int indicator, double[][][] mean, double[][][] stdDev) throws IOException {
		FileWriter os = new FileWriter(fileName, true);
		os.write("\\" + "\n");
		os.write("\\begin{table*}" + "\n");
		os.write("\\caption{" + indicatorList_[indicator] + ". Mean and standard deviation}" + "\n");
		os.write("\\label{table:mean." + indicatorList_[indicator] + "}" + "\n");
		os.write("\\centering" + "\n");
		os.write("\\begin{tiny}" + "\n");
		os.write("\\begin{tabular}{l");

		// calculate the number of columns
        for (String anAlgorithmNameList_ : algorithmNameList_) {
            os.write("l");
        }
		os.write("}\n");

		os.write("\\hline");
		// write table head
		
	
		int numberofalg = 0;
		final int  numberOfalgforEachrow = 11;
		int cycles = 0;
		if (algorithmNameList_.length <=numberOfalgforEachrow){
			numberofalg = algorithmNameList_.length;
			cycles = algorithmNameList_.length/numberofalg;
		} else {	
			numberofalg = numberOfalgforEachrow;
			if(algorithmNameList_.length%numberofalg==0)
				cycles = algorithmNameList_.length/numberofalg;
			else
				cycles = algorithmNameList_.length/numberofalg+1;
		}
		
        for (int cyc=0;cyc<cycles;cyc++) {
        	
        	for (int i = -1; i < numberofalg; i++) {
        		if(cyc*numberofalg+i==algorithmNameList_.length){
        			os.write( " \\\\ "+ "\n");
        			break;
        		}
    			if (i == -1) {
    				os.write(" & ");
    			} else if (i == (numberofalg - 1)) {
    				os.write(" " + algorithmNameList_[cyc*numberofalg+i] + "\\\\" + "\n");
    			} else {
    				os.write("" + algorithmNameList_[cyc*numberofalg+i] + " & ");
    			}
    		}
        	os.write("\\hline" + "\n");
			String m, s;
			// write lines
			for (int i = 0; i < problemList_.length; i++) {
				// find the best value and second best value
				double bestValue       ;
				double bestValueIQR    ;
				double secondBestValue ;
				double secondBestValueIQR ;
				int bestIndex = -1 ;
				int secondBestIndex = -1 ;
				if ((Boolean) indicatorMinimize_.get(indicatorList_[indicator])) {// minimize by default
					bestValue = Double.MAX_VALUE;
					bestValueIQR = Double.MAX_VALUE;
					secondBestValue = Double.MAX_VALUE;
					secondBestValueIQR = Double.MAX_VALUE;
					for (int j = 0; j < (algorithmNameList_.length); j++) {
						if ((mean[indicator][i][j] < bestValue) ||
								((mean[indicator][i][j] == bestValue) && (stdDev[indicator][i][j] < bestValueIQR))) {
							secondBestIndex = bestIndex ;
							secondBestValue = bestValue ;
							secondBestValueIQR = bestValueIQR ;
							bestValue = mean[indicator][i][j];
							bestValueIQR = stdDev[indicator][i][j];
							bestIndex = j;
						}
						else if ((mean[indicator][i][j] < secondBestValue) ||
								((mean[indicator][i][j] == secondBestValue) && (stdDev[indicator][i][j] < secondBestValueIQR))) {
							secondBestIndex = j ;
							secondBestValue = mean[indicator][i][j] ;
							secondBestValueIQR = stdDev[indicator][i][j] ;
						} // else if
					}
				} // if
				else { // indicator to maximize e.g., the HV
					bestValue = Double.MIN_VALUE;
					bestValueIQR = Double.MIN_VALUE;
					secondBestValue = Double.MIN_VALUE;
					secondBestValueIQR = Double.MIN_VALUE;
					for (int j = 0; j < (algorithmNameList_.length); j++) {
						if ((mean[indicator][i][j] > bestValue) ||
								((mean[indicator][i][j] == bestValue) && (stdDev[indicator][i][j] < bestValueIQR))) {
							secondBestIndex = bestIndex ;
							secondBestValue = bestValue ;
							secondBestValueIQR = bestValueIQR ;
							bestValue = mean[indicator][i][j];
							bestValueIQR = stdDev[indicator][i][j];
							bestIndex = j;
						}
						else if ((mean[indicator][i][j] > secondBestValue) ||
								((mean[indicator][i][j] == secondBestValue) && (stdDev[indicator][i][j] < secondBestValueIQR))) {
							secondBestIndex = j ;
							secondBestValue = mean[indicator][i][j] ;
							secondBestValueIQR = stdDev[indicator][i][j] ;
						} // else if
					} // for
				} // else
	
				os.write(problemList_[i].replace("_", "\\_") + " & ");
				if (cyc<cycles-1) {
					for (int j = cyc*numberofalg; j < (cyc+1)*numberofalg  ; j++) {
						if (j == bestIndex) {
							os.write("\\cellcolor{gray95}");
						}
						if (j == secondBestIndex) {
							os.write("\\cellcolor{gray25}");
						}
		                if(j<(cyc+1)*numberofalg -1 ) {
							m = String.format(Locale.ENGLISH, "%.3e", mean[indicator][i][j]);
							s = String.format(Locale.ENGLISH, "%.1e", stdDev[indicator][i][j]);
							os.write("$" + m + "(" + s + ")$ & ");
		                }else{
		                	m = String.format(Locale.ENGLISH, "%.3e", mean[indicator][i][j]);
							s = String.format(Locale.ENGLISH, "%.1e", stdDev[indicator][i][j]);
//							os.write("$" + m + "_{" + s + "}$ \\\\" + "\n");
							os.write("$" + m + "~(" + s + ")$ \\\\" + "\n");
							
		                }
					}
					
//					if (bestIndex == ((cyc+1)*numberofalg - 1)) {
//						os.write("\\cellcolor{gray95}");
//					}
//					m = String.format(Locale.ENGLISH, "%8.3e", mean[indicator][i][(cyc+1)*numberofalg - 1]);
//					s = String.format(Locale.ENGLISH, "%8.1e", stdDev[indicator][i][(cyc+1)*numberofalg - 1]);
//					os.write("$" + m + "_{" + s + "}$ \\\\" + "\n");
					
				}else {
					for (int j = cyc*numberofalg; j < (cyc+1)*numberofalg-1; j++) {
						if (j == bestIndex) {
							os.write("\\cellcolor{gray95}");
						}
						if (j == secondBestIndex) {
							os.write("\\cellcolor{gray25}");
						}
		
						m = String.format(Locale.ENGLISH, "%.3E", mean[indicator][i][j]);
						s = String.format(Locale.ENGLISH, "%.2E", stdDev[indicator][i][j]);
//						m = String.format("%.3E", mean[indicator][i][j]);
//						s = String.format("%.1E", stdDev[indicator][i][j]);
						
//						os.write("$" + m + "_{" + s + "}$ & ");
						os.write("$" + m + " $ ($" + s + "$) &");
						
					}
				}//if
				if(cyc == cycles -1 ){
					if (bestIndex == (algorithmNameList_.length - 1)) {
						os.write("\\cellcolor{gray95}");
					}
					m = String.format(Locale.ENGLISH, "%.3E", mean[indicator][i][algorithmNameList_.length - 1]);
					s = String.format(Locale.ENGLISH, "%.2E", stdDev[indicator][i][algorithmNameList_.length - 1]);
//					os.write("$" + m + "_{" + s + "}$ \\\\" + "\n");
					os.write("$" + m + "$ ($" + s + "$) \\\\" + "\n");
				}
			} // for
			os.write("\\hline" + "\n");
        }//for 
		//os.write("" + mean[0][problemList_.length-1][algorithmNameList_.length-1] + "\\\\"+ "\n" ) ;

//		os.write("\\hline" + "\n");
		os.write("\\end{tabular}" + "\n");
		os.write("\\end{tiny}" + "\n");
		os.write("\\end{table*}" + "\n");
		os.close();
	} // printMeanStdDev
	
	/**
	 * Without std Dev values
	 * @param fileName
	 * @param indicator
	 * @param mean
	 * @param stdDev
	 * @throws IOException
	 */
	void printMeanStdDev(String fileName, int indicator, double[][][] mean) throws IOException {
		FileWriter os = new FileWriter(fileName, true);
		os.write("\\" + "\n");
		os.write("\\begin{table*}" + "\n");
		os.write("\\caption{" + indicatorList_[indicator] + ". Mean and standard deviation}" + "\n");
		os.write("\\label{table:mean." + indicatorList_[indicator] + "}" + "\n");
		os.write("\\centering" + "\n");
		os.write("\\begin{tiny}" + "\n");
		os.write("\\begin{tabular}{l");

		// calculate the number of columns
        for (String anAlgorithmNameList_ : algorithmNameList_) {
            os.write("l");
        }
		os.write("}\n");

		os.write("\\hline");
		// write table head
		
	
		int numberofalg = 0;
		final int  numberOfalgforEachrow = 11;
		int cycles = 0;
		if (algorithmNameList_.length <=numberOfalgforEachrow){
			numberofalg = algorithmNameList_.length;
			cycles = algorithmNameList_.length/numberofalg;
		} else {	
			numberofalg = numberOfalgforEachrow;
			if(algorithmNameList_.length%numberofalg==0)
				cycles = algorithmNameList_.length/numberofalg;
			else
				cycles = algorithmNameList_.length/numberofalg+1;
		}
		
        for (int cyc=0;cyc<cycles;cyc++) {
        	
        	for (int i = -1; i < numberofalg; i++) {
        		if(cyc*numberofalg+i==algorithmNameList_.length){
        			os.write( " \\\\ "+ "\n");
        			break;
        		}
    			if (i == -1) {
    				os.write(" & ");
    			} else if (i == (numberofalg - 1)) {
    				os.write(" " + algorithmNameList_[cyc*numberofalg+i] + "\\\\" + "\n");
    			} else {
    				os.write("" + algorithmNameList_[cyc*numberofalg+i] + " & ");
    			}
    		}
        	os.write("\\hline" + "\n");
			String m, s;
			// write lines
			for (int i = 0; i < problemList_.length; i++) {
				// find the best value and second best value
				double bestValue       ;
				double bestValueIQR    ;
				double secondBestValue ;
				double secondBestValueIQR ;
				int bestIndex = -1 ;
				int secondBestIndex = -1 ;
				if ((Boolean) indicatorMinimize_.get(indicatorList_[indicator])) {// minimize by default
					bestValue = Double.MAX_VALUE;
					bestValueIQR = Double.MAX_VALUE;
					secondBestValue = Double.MAX_VALUE;
					secondBestValueIQR = Double.MAX_VALUE;
					for (int j = 0; j < (algorithmNameList_.length); j++) {
						if ((mean[indicator][i][j] < bestValue) ) {
							secondBestIndex = bestIndex ;
							secondBestValue = bestValue ;
							secondBestValueIQR = bestValueIQR ;
							bestValue = mean[indicator][i][j];						
							bestIndex = j;
						}
						else if ((mean[indicator][i][j] < secondBestValue) ) {
							secondBestIndex = j ;
							secondBestValue = mean[indicator][i][j] ;						
						} // else if
					}
				} // if
				else { // indicator to maximize e.g., the HV
					bestValue = Double.MIN_VALUE;
					bestValueIQR = Double.MIN_VALUE;
					secondBestValue = Double.MIN_VALUE;
					secondBestValueIQR = Double.MIN_VALUE;
					for (int j = 0; j < (algorithmNameList_.length); j++) {
						if ((mean[indicator][i][j] > bestValue) ) {
							secondBestIndex = bestIndex ;
							secondBestValue = bestValue ;
							secondBestValueIQR = bestValueIQR ;
							bestValue = mean[indicator][i][j];
							bestIndex = j;
						}
						else if ((mean[indicator][i][j] > secondBestValue) ) {
							secondBestIndex = j ;
							secondBestValue = mean[indicator][i][j] ;							
						} // else if
					} // for
				} // else
	
				os.write(problemList_[i].replace("_", "\\_") + " & ");
				if (cyc<cycles-1) {
					for (int j = cyc*numberofalg; j < (cyc+1)*numberofalg  ; j++) {
						if (j == bestIndex) {
							os.write("\\cellcolor{gray95}");
						}
						if (j == secondBestIndex) {
							os.write("\\cellcolor{gray25}");
						}
		                if(j<(cyc+1)*numberofalg -1 ) {
							m = String.format(Locale.ENGLISH, "%.4e", mean[indicator][i][j]);							
							os.write("$" + m + "$ & ");
		                }else{
		                	m = String.format(Locale.ENGLISH, "%.4e", mean[indicator][i][j]);
							os.write("$" + m + "$ \\\\" + "\n");
							
		                }
					}					

					
				}else {
					for (int j = cyc*numberofalg; j < (cyc+1)*numberofalg-1; j++) {
						if (j == bestIndex) {
							os.write("\\cellcolor{gray95}");
						}
						if (j == secondBestIndex) {
							os.write("\\cellcolor{gray25}");
						}
		
						m = String.format(Locale.ENGLISH, "%.4e", mean[indicator][i][j]);						
						os.write("$" + m + "$ & ");
						
					}
				}//if
				if(cyc == cycles -1 ){
					if (bestIndex == (algorithmNameList_.length - 1)) {
						os.write("\\cellcolor{gray95}");
					}
					if (secondBestIndex == (algorithmNameList_.length - 1)) {
						os.write("\\cellcolor{gray25}");
					}
					m = String.format(Locale.ENGLISH, "%.4e", mean[indicator][i][algorithmNameList_.length - 1]);
					os.write("$" + m + "$ \\\\" + "\n");
				}
			} // for
			os.write("\\hline" + "\n");
        }//for 
		//os.write("" + mean[0][problemList_.length-1][algorithmNameList_.length-1] + "\\\\"+ "\n" ) ;

//		os.write("\\hline" + "\n");
		os.write("\\end{tabular}" + "\n");
		os.write("\\end{tiny}" + "\n");
		os.write("\\end{table*}" + "\n");
		os.close();
	} // printMeanStdDev
	
	void printMeanforTest(String fileName, int indicator, double[][][] mean) throws IOException {
		resetFile(fileName);
		FileWriter os = new FileWriter(fileName, true);
		String m;		
			
//		os.write("Indicator:"+indicatorList_[indicator]+".mean");
//		os.write("\n");
		os.write("Problmes,");
		 for(int i=0;i<algorithmNameList_.length-1;i++) 
			 os.write(algorithmNameList_[i].toString()+",");
		 
		 os.write(algorithmNameList_[algorithmNameList_.length-1].toString()+",");
		 os.write("\n");
		
		for(int i=0;i<problemList_.length;i++){//for each problem
			os.write(problemList_[i]+",");
			for(int j=0;j<algorithmNameList_.length;j++){//for each algorithm
				m = String.format(Locale.ENGLISH, "%10.3e", mean[indicator][i][j]);
				if(j==algorithmNameList_.length){
					os.write("\n");
				}
				else
					os.write(m+",");
			}
			os.write("\n");
		}
		
		os.write("\n");		

		os.close();
	} // printMeanforTest
	
	
	/**
	 * Pring median and IQR
	 * @param fileName
	 * @param indicator
	 * @param median
	 * @param IQR
	 * @throws IOException
	 */
	void printMedianIQR(String fileName, int indicator, double[][][] median, double[][][] IQR) throws IOException {
		FileWriter os = new FileWriter(fileName, true);
		os.write("\\" + "\n");
		os.write("\\begin{table*}" + "\n");
		os.write("\\caption{" + indicatorList_[indicator] + ". Median and IQR}" + "\n");
		os.write("\\label{table:median." + indicatorList_[indicator] + "}" + "\n");
		os.write("\\begin{tiny}" + "\n");
		os.write("\\centering" + "\n");
		os.write("\\begin{tabular}{l");

		// calculate the number of columns
        for (String anAlgorithmNameList_ : algorithmNameList_) {
            os.write("l");
        }
		os.write("}\n");

		os.write("\\hline");
		// write table head
		int numberofalg = 0;
		final int  numberOfalgforEachrow = 11;
		int cycles = 0;
		if (algorithmNameList_.length <=numberOfalgforEachrow){
			numberofalg = algorithmNameList_.length;
			cycles = algorithmNameList_.length/numberofalg;
		} else {	
			numberofalg = numberOfalgforEachrow;
			if(algorithmNameList_.length%numberofalg==0)
				cycles = algorithmNameList_.length/numberofalg;
			else
				cycles = algorithmNameList_.length/numberofalg+1;
		}
		
        for (int cyc=0;cyc<cycles;cyc++) {
        	
        	for (int i = -1; i < numberofalg; i++) {        		
            		if(cyc*numberofalg+i==algorithmNameList_.length){
            			os.write( " \\\\ "+ "\n");
            			break;
            		}
    			if (i == -1) {
    				os.write(" & ");
    			} else if (i == (numberofalg - 1)) {
    				os.write(" " + algorithmNameList_[cyc*numberofalg+i] + "\\\\" + "\n");
    			} else {
    				os.write("" + algorithmNameList_[cyc*numberofalg+i] + " & ");
    			}
    		}
        	os.write("\\hline" + "\n");
			String m, s;
			// write lines
			for (int i = 0; i < problemList_.length; i++) {
				// find the best value and second best value
				double bestValue       ;
				double bestValueIQR    ;
				double secondBestValue ;
				double secondBestValueIQR ;
				int bestIndex = -1 ;
				int secondBestIndex = -1 ;
				if ((Boolean) indicatorMinimize_.get(indicatorList_[indicator])) {// minimize by default
					bestValue = Double.MAX_VALUE;
					bestValueIQR = Double.MAX_VALUE;
					secondBestValue = Double.MAX_VALUE;
					secondBestValueIQR = Double.MAX_VALUE;
					for (int j = 0; j < (algorithmNameList_.length); j++) {
						if ((median[indicator][i][j] < bestValue) ||
								((median[indicator][i][j] == bestValue) && (IQR[indicator][i][j] < bestValueIQR))) {
							secondBestIndex = bestIndex ;
							secondBestValue = bestValue ;
							secondBestValueIQR = bestValueIQR ;
							bestValue = median[indicator][i][j];
							bestValueIQR = IQR[indicator][i][j];
							bestIndex = j;
						}
						else if ((median[indicator][i][j] < secondBestValue) ||
								((median[indicator][i][j] == secondBestValue) && (IQR[indicator][i][j] < secondBestValueIQR))) {
							secondBestIndex = j ;
							secondBestValue = median[indicator][i][j] ;
							secondBestValueIQR = IQR[indicator][i][j] ;
						} // else if
					} // for
				} // if
				else { // indicator to maximize e.g., the HV
					bestValue = Double.MIN_VALUE;
					bestValueIQR = Double.MIN_VALUE;
					secondBestValue = Double.MIN_VALUE;
					secondBestValueIQR = Double.MIN_VALUE;
					for (int j = 0; j < (algorithmNameList_.length); j++) {
						if ((median[indicator][i][j] > bestValue) ||
								((median[indicator][i][j] == bestValue) && (IQR[indicator][i][j] < bestValueIQR))) {
							secondBestIndex = bestIndex ;
							secondBestValue = bestValue ;
							secondBestValueIQR = bestValueIQR ;
							bestValue = median[indicator][i][j];
							bestValueIQR = IQR[indicator][i][j];
							bestIndex = j;
						}
						else if ((median[indicator][i][j] > secondBestValue) ||
								((median[indicator][i][j] == secondBestValue) && (IQR[indicator][i][j] < secondBestValueIQR))) {
							secondBestIndex = j ;
							secondBestValue = median[indicator][i][j] ;
							secondBestValueIQR = IQR[indicator][i][j] ;
						} // else if
					} // for
				} // else
	
				os.write(problemList_[i].replace("_", "\\_") + " & ");
				if (cyc<cycles-1) { 
				for (int j = cyc*numberofalg; j < (cyc+1)*numberofalg ; j++) {
					if (j == bestIndex) {
						os.write("\\cellcolor{gray95}");
					}
					if (j == secondBestIndex) {
						os.write("\\cellcolor{gray25}");
					}
					if(j<(cyc+1)*numberofalg -1 ) {
						m = String.format(Locale.ENGLISH, "%7.3E", median[indicator][i][j]);
						s = String.format(Locale.ENGLISH, "%5.1E", IQR[indicator][i][j]);
						os.write("$" + m + "~(" + s + ")$ & ");
					} else {
						m = String.format(Locale.ENGLISH, "%7.3E", median[indicator][i][j]);
						s = String.format(Locale.ENGLISH, "%5.1E", IQR[indicator][i][j]);
//						os.write("$" + m + "_{" + s + "}$ \\\\" + "\n");
						os.write("$" + m + "~(" + s + ")$ \\\\" + "\n");
					}
					
				}
				}else {
					for (int j = cyc*numberofalg; j < (cyc+1)*numberofalg-1; j++) {
						if (j == bestIndex) {
							os.write("\\cellcolor{gray95}");
						}
						if (j == secondBestIndex) {
							os.write("\\cellcolor{gray25}");
						}
		
						m = String.format(Locale.ENGLISH, "%7.3E", median[indicator][i][j]);
						s = String.format(Locale.ENGLISH, "%5.1E", IQR[indicator][i][j]);
//						os.write("$" + m + "_{" + s + "}$ & ");
						os.write("$" + m + "~(" + s + ")$ & ");
					}
				}//if
				if(cyc == cycles -1 ){
					if (bestIndex == (algorithmNameList_.length - 1)) {
						os.write("\\cellcolor{gray95}");
					}
					if (secondBestIndex == (algorithmNameList_.length - 1)) {
						os.write("\\cellcolor{gray25}");
					}
					m = String.format(Locale.ENGLISH, "%7.3E", median[indicator][i][algorithmNameList_.length - 1]);
					s = String.format(Locale.ENGLISH, "%5.1E", IQR[indicator][i][algorithmNameList_.length - 1]);
//					os.write("$" + m + "_{" + s + "}$ \\\\" + "\n");
					os.write("$" + m + "~(" + s + ")$ \\\\" + "\n");
				}
			} // for
			os.write("\\hline" + "\n");
        }//for
		//os.write("" + mean[0][problemList_.length-1][algorithmNameList_.length-1] + "\\\\"+ "\n" ) ;

//		os.write("\\hline" + "\n");
		os.write("\\end{tabular}" + "\n");
		os.write("\\end{tiny}" + "\n");
		os.write("\\end{table*}" + "\n");
		os.close();
	} // printMedianIQR

	
	/**
	 * Pring median and IQR
	 * @param fileName
	 * @param indicator
	 * @param median
	 * @param IQR
	 * @throws IOException
	 */
	void printMedian(String fileName, int indicator, double[][][] median) throws IOException {
		FileWriter os = new FileWriter(fileName, true);
		os.write("\\" + "\n");
		os.write("\\begin{table*}" + "\n");
		os.write("\\caption{" + indicatorList_[indicator] + ". Median}" + "\n");
		os.write("\\label{table:median." + indicatorList_[indicator] + "}" + "\n");
		os.write("\\begin{tiny}" + "\n");
		os.write("\\centering" + "\n");
		os.write("\\begin{tabular}{l");

		// calculate the number of columns
        for (String anAlgorithmNameList_ : algorithmNameList_) {
            os.write("l");
        }
		os.write("}\n");

		os.write("\\hline");
		// write table head
		int numberofalg = 0;
		final int  numberOfalgforEachrow = 11;
		int cycles = 0;
		if (algorithmNameList_.length <=numberOfalgforEachrow){
			numberofalg = algorithmNameList_.length;
			cycles = algorithmNameList_.length/numberofalg;
		} else {	
			numberofalg = numberOfalgforEachrow;
			if(algorithmNameList_.length%numberofalg==0)
				cycles = algorithmNameList_.length/numberofalg;
			else
				cycles = algorithmNameList_.length/numberofalg+1;
		}
		
        for (int cyc=0;cyc<cycles;cyc++) {
        	
        	for (int i = -1; i < numberofalg; i++) {        		
            		if(cyc*numberofalg+i==algorithmNameList_.length){
            			os.write( " \\\\ "+ "\n");
            			break;
            		}
    			if (i == -1) {
    				os.write(" & ");
    			} else if (i == (numberofalg - 1)) {
    				os.write(" " + algorithmNameList_[cyc*numberofalg+i] + "\\\\" + "\n");
    			} else {
    				os.write("" + algorithmNameList_[cyc*numberofalg+i] + " & ");
    			}
    		}
        	os.write("\\hline" + "\n");
			String m, s;
			// write lines
			for (int i = 0; i < problemList_.length; i++) {
				// find the best value and second best value
				double bestValue       ;
				double bestValueIQR    ;
				double secondBestValue ;
				double secondBestValueIQR ;
				int bestIndex = -1 ;
				int secondBestIndex = -1 ;
				if ((Boolean) indicatorMinimize_.get(indicatorList_[indicator])) {// minimize by default
					bestValue = Double.MAX_VALUE;
					bestValueIQR = Double.MAX_VALUE;
					secondBestValue = Double.MAX_VALUE;
					secondBestValueIQR = Double.MAX_VALUE;
					for (int j = 0; j < (algorithmNameList_.length); j++) {
						if ((median[indicator][i][j] < bestValue) ) {
							secondBestIndex = bestIndex ;
							secondBestValue = bestValue ;
							secondBestValueIQR = bestValueIQR ;
							bestValue = median[indicator][i][j];					
							bestIndex = j;
						}
						else if ((median[indicator][i][j] < secondBestValue) ) {
							secondBestIndex = j ;
							secondBestValue = median[indicator][i][j] ;							
						} // else if
					} // for
				} // if
				else { // indicator to maximize e.g., the HV
					bestValue = Double.MIN_VALUE;
					bestValueIQR = Double.MIN_VALUE;
					secondBestValue = Double.MIN_VALUE;
					secondBestValueIQR = Double.MIN_VALUE;
					for (int j = 0; j < (algorithmNameList_.length); j++) {
						if ((median[indicator][i][j] > bestValue)) {
							secondBestIndex = bestIndex ;
							secondBestValue = bestValue ;
							secondBestValueIQR = bestValueIQR ;
							bestValue = median[indicator][i][j];						
							bestIndex = j;
						}
						else if ((median[indicator][i][j] > secondBestValue) ) {
							secondBestIndex = j ;
							secondBestValue = median[indicator][i][j] ;						
						} // else if
					} // for
				} // else
	
				os.write(problemList_[i].replace("_", "\\_") + " & ");
				if (cyc < cycles-1) { 
					for (int j = cyc*numberofalg; j < (cyc+1)*numberofalg ; j++) {
						if (j == bestIndex) {
							os.write("\\cellcolor{gray95}");
						}
						if (j == secondBestIndex) {
							os.write("\\cellcolor{gray25}");
						}
						if(j<(cyc+1)*numberofalg -1 ) {
							m = String.format(Locale.ENGLISH, "%.4E", median[indicator][i][j]);	
							os.write("$" + m + "$ $ $ & ");
						} else {
							m = String.format(Locale.ENGLISH, "%.4E", median[indicator][i][j]);					
							os.write("$" + m + "$ $ $\\\\" + "\n");
						}
						
					}
				/* ----------------------This is the most important part-------------------------------*/
				}else {
					for (int j = cyc*numberofalg; j < (cyc+1)*numberofalg-1; j++) {
						if (j == bestIndex) {
							os.write("\\cellcolor{gray95}");
						}
						if (j == secondBestIndex) {
							os.write("\\cellcolor{gray25}");
						}
		
						m = String.format(Locale.ENGLISH, "%.4E", median[indicator][i][j]);		
						if (j == 0) {
							os.write("$" + m + "$ & ");
						} else {
							os.write("$" + m + "$$\\oplus$ & ");
						}
					}
				}//if
				
				if(cyc == cycles -1 ){
					if (bestIndex == (algorithmNameList_.length - 1)) {
						os.write("\\cellcolor{gray95}");
					}
					if (algorithmNameList_.length - 1 == secondBestIndex) {
						os.write("\\cellcolor{gray25}");
					}
					
					m = String.format(Locale.ENGLISH, "%.4E", median[indicator][i][algorithmNameList_.length - 1]);						
					os.write("$" + m + "$$\\oplus$ \\\\" + "\n");
				}				
				/*  ----------------------This is the most important part-------------------------------*/
				
			} // for
			os.write("\\hline" + "\n");
        }//for
        
		//os.write("" + mean[0][problemList_.length-1][algorithmNameList_.length-1] + "\\\\"+ "\n" ) ;

//		os.write("\\hline" + "\n");
		os.write("\\end{tabular}" + "\n");
		os.write("\\end{tiny}" + "\n");
		os.write("\\end{table*}" + "\n");
		os.close();
	} // printMedian
	
	/**
	 * Pring median and IQR
	 * @param fileName
	 * @param indicator
	 * @param median
	 * @param IQR
	 * @throws IOException
	 */
	void printMedianSymbols(String fileName, int indicator, double[][][] median, String [][][] symbols) throws IOException {
		FileWriter os = new FileWriter(fileName, true);
		os.write("\\" + "\n");
		os.write("\\begin{table*}" + "\n");
		os.write("\\caption{" + indicatorList_[indicator] + ". Median}" + "\n");
		os.write("\\label{table:median." + indicatorList_[indicator] + "}" + "\n");
		os.write("\\begin{tiny}" + "\n");
		os.write("\\centering" + "\n");
		os.write("\\begin{tabular}{l");

		// calculate the number of columns
        for (String anAlgorithmNameList_ : algorithmNameList_) {
            os.write("l");
        }
		os.write("}\n");

		os.write("\\hline");
		// write table head
		int numberofalg = 0;
		final int  numberOfalgforEachrow = 11;
		int cycles = 0;
		if (algorithmNameList_.length <=numberOfalgforEachrow){
			numberofalg = algorithmNameList_.length;
			cycles = algorithmNameList_.length/numberofalg;
		} else {	
			numberofalg = numberOfalgforEachrow;
			if(algorithmNameList_.length%numberofalg==0)
				cycles = algorithmNameList_.length/numberofalg;
			else
				cycles = algorithmNameList_.length/numberofalg+1;
		}
		
        for (int cyc=0;cyc<cycles;cyc++) {
        	
        	for (int i = -1; i < numberofalg; i++) {        		
            		if(cyc*numberofalg+i==algorithmNameList_.length){
            			os.write( " \\\\ "+ "\n");
            			break;
            		}
    			if (i == -1) {
    				os.write(" & ");
    			} else if (i == (numberofalg - 1)) {
    				os.write(" " + algorithmNameList_[cyc*numberofalg+i] + "\\\\" + "\n");
    			} else {
    				os.write("" + algorithmNameList_[cyc*numberofalg+i] + " & ");
    			}
    		}
        	os.write("\\hline" + "\n");
			String m, s;
			// write lines
			for (int i = 0; i < problemList_.length; i++) {
				// find the best value and second best value
				double bestValue       ;
				double bestValueIQR    ;
				double secondBestValue ;
				double secondBestValueIQR ;
				int bestIndex = -1 ;
				int secondBestIndex = -1 ;
				if ((Boolean) indicatorMinimize_.get(indicatorList_[indicator])) {// minimize by default
					bestValue = Double.MAX_VALUE;
					bestValueIQR = Double.MAX_VALUE;
					secondBestValue = Double.MAX_VALUE;
					secondBestValueIQR = Double.MAX_VALUE;
					for (int j = 0; j < (algorithmNameList_.length); j++) {
						if ((median[indicator][i][j] < bestValue) ) {
							secondBestIndex = bestIndex ;
							secondBestValue = bestValue ;
							secondBestValueIQR = bestValueIQR ;
							bestValue = median[indicator][i][j];					
							bestIndex = j;
						}
						else if ((median[indicator][i][j] < secondBestValue) ) {
							secondBestIndex = j ;
							secondBestValue = median[indicator][i][j] ;							
						} // else if
					} // for
				} // if
				else { // indicator to maximize e.g., the HV
					bestValue = Double.MIN_VALUE;
					bestValueIQR = Double.MIN_VALUE;
					secondBestValue = Double.MIN_VALUE;
					secondBestValueIQR = Double.MIN_VALUE;
					for (int j = 0; j < (algorithmNameList_.length); j++) {
						if ((median[indicator][i][j] > bestValue)) {
							secondBestIndex = bestIndex ;
							secondBestValue = bestValue ;
							secondBestValueIQR = bestValueIQR ;
							bestValue = median[indicator][i][j];						
							bestIndex = j;
						}
						else if ((median[indicator][i][j] > secondBestValue) ) {
							secondBestIndex = j ;
							secondBestValue = median[indicator][i][j] ;						
						} // else if
					} // for
				} // else
	
				os.write(problemList_[i].replace("_", "\\_") + " & ");
				if (cyc < cycles-1) { 
					for (int j = cyc*numberofalg; j < (cyc+1)*numberofalg ; j++) {
						if (j == bestIndex) {
							os.write("\\cellcolor{gray95}");
						}
						if (j == secondBestIndex) {
							os.write("\\cellcolor{gray25}");
						}
						if(j<(cyc+1)*numberofalg -1 ) {
							m = String.format(Locale.ENGLISH, "%.4E", median[indicator][i][j]);	
							os.write("$" + m + "$ $ $ & ");
						} else {
							m = String.format(Locale.ENGLISH, "%.4E", median[indicator][i][j]);					
							os.write("$" + m + "$ $ $\\\\" + "\n");
						}
						
					}
					
				///////---------------------This is the most important part-------------------------------*/
				}else {
					for (int j = cyc*numberofalg; j < (cyc+1)*numberofalg-1; j++) {
						if (j == bestIndex) {
							os.write("\\cellcolor{gray95}");
						}
						if (j == secondBestIndex) {
							os.write("\\cellcolor{gray25}");
						}
		
						m = String.format(Locale.ENGLISH, "%.4E", median[indicator][i][j]);		
						if (j == 0) {
							os.write("$" + m + "$ & ");
						} else {
							
							String temp;
							if ("+".equalsIgnoreCase(symbols[indicator][i][j] ))
								temp = "\\oplus";
							else if ("-".equalsIgnoreCase(symbols[indicator][i][j] )) {
								temp = "\\ominus";
							} else if ("=".equalsIgnoreCase(symbols[indicator][i][j])){
								temp = "\\approx";
							} else {
								temp = "Null";
							}
							os.write("$" + m + "$$" + temp + " $ & ");
						}
					}
				}//if
				
				if(cyc == cycles - 1 ){
					if (bestIndex == (algorithmNameList_.length - 1)) {
						os.write("\\cellcolor{gray95}");
					}
					if (algorithmNameList_.length - 1 == secondBestIndex) {
						os.write("\\cellcolor{gray25}");
					}
					
					m = String.format(Locale.ENGLISH, "%.4E", median[indicator][i][algorithmNameList_.length - 1]);	
					
					String temp;
					if ("+".equalsIgnoreCase(symbols[indicator][i][algorithmNameList_.length - 1] ))
						temp = "\\oplus";
					else if ("-".equalsIgnoreCase(symbols[indicator][i][algorithmNameList_.length - 1] )) {
						temp = "\\ominus";
					} else if ("=".equalsIgnoreCase(symbols[indicator][i][algorithmNameList_.length - 1])){
						temp = "\\approx";
					} else {
						temp = "Null";
					}
					
					os.write("$" + m + "$$" + temp + "$ \\\\" + "\n");
				}				
				////----------------------This is the most important part-------------------------------*/
				
			} // for
			os.write("\\hline" + "\n");
        }//for
        
		//os.write("" + mean[0][problemList_.length-1][algorithmNameList_.length-1] + "\\\\"+ "\n" ) ;

//		os.write("\\hline" + "\n");
		os.write("\\end{tabular}" + "\n");
		os.write("\\end{tiny}" + "\n");
		os.write("\\end{table*}" + "\n");
		os.close();
	} // printMedian
	
	/**
	 * Pring median and IQR
	 * @param fileName
	 * @param indicator
	 * @param median
	 * @param IQR
	 * @throws IOException
	 */
	void printMeanSymbols(String fileName, int indicator, double[][][] median, String [][][] symbols) throws IOException {
		FileWriter os = new FileWriter(fileName, true);
		os.write("\\" + "\n");
		os.write("\\begin{table*}" + "\n");
		os.write("\\caption{" + indicatorList_[indicator] + ". Mean}" + "\n");
		os.write("\\label{table:median." + indicatorList_[indicator] + "}" + "\n");
		os.write("\\begin{tiny}" + "\n");
		os.write("\\centering" + "\n");
		os.write("\\begin{tabular}{l");

		// calculate the number of columns
        for (String anAlgorithmNameList_ : algorithmNameList_) {
            os.write("l");
        }
		os.write("}\n");

		os.write("\\hline");
		// write table head
		int numberofalg = 0;
		final int  numberOfalgforEachrow = 11;
		int cycles = 0;
		if (algorithmNameList_.length <=numberOfalgforEachrow){
			numberofalg = algorithmNameList_.length;
			cycles = algorithmNameList_.length/numberofalg;
		} else {	
			numberofalg = numberOfalgforEachrow;
			if(algorithmNameList_.length%numberofalg==0)
				cycles = algorithmNameList_.length/numberofalg;
			else
				cycles = algorithmNameList_.length/numberofalg+1;
		}
		
        for (int cyc=0;cyc<cycles;cyc++) {
        	
        	for (int i = -1; i < numberofalg; i++) {        		
            		if(cyc*numberofalg+i==algorithmNameList_.length){
            			os.write( " \\\\ "+ "\n");
            			break;
            		}
    			if (i == -1) {
    				os.write(" & ");
    			} else if (i == (numberofalg - 1)) {
    				os.write(" " + algorithmNameList_[cyc*numberofalg+i] + "\\\\" + "\n");
    			} else {
    				os.write("" + algorithmNameList_[cyc*numberofalg+i] + " & ");
    			}
    		}
        	os.write("\\hline" + "\n");
			String m, s;
			// write lines
			for (int i = 0; i < problemList_.length; i++) {
				// find the best value and second best value
				double bestValue       ;
				double bestValueIQR    ;
				double secondBestValue ;
				double secondBestValueIQR ;
				int bestIndex = -1 ;
				int secondBestIndex = -1 ;
				if ((Boolean) indicatorMinimize_.get(indicatorList_[indicator])) {// minimize by default
					bestValue = Double.MAX_VALUE;
					bestValueIQR = Double.MAX_VALUE;
					secondBestValue = Double.MAX_VALUE;
					secondBestValueIQR = Double.MAX_VALUE;
					for (int j = 0; j < (algorithmNameList_.length); j++) {
						if ((median[indicator][i][j] < bestValue) ) {
							secondBestIndex = bestIndex ;
							secondBestValue = bestValue ;
							secondBestValueIQR = bestValueIQR ;
							bestValue = median[indicator][i][j];					
							bestIndex = j;
						}
						else if ((median[indicator][i][j] < secondBestValue) ) {
							secondBestIndex = j ;
							secondBestValue = median[indicator][i][j] ;							
						} // else if
					} // for
				} // if
				else { // indicator to maximize e.g., the HV
					bestValue = Double.MIN_VALUE;
					bestValueIQR = Double.MIN_VALUE;
					secondBestValue = Double.MIN_VALUE;
					secondBestValueIQR = Double.MIN_VALUE;
					for (int j = 0; j < (algorithmNameList_.length); j++) {
						if ((median[indicator][i][j] > bestValue)) {
							secondBestIndex = bestIndex ;
							secondBestValue = bestValue ;
							secondBestValueIQR = bestValueIQR ;
							bestValue = median[indicator][i][j];						
							bestIndex = j;
						}
						else if ((median[indicator][i][j] > secondBestValue) ) {
							secondBestIndex = j ;
							secondBestValue = median[indicator][i][j] ;						
						} // else if
					} // for
				} // else
	
				os.write(problemList_[i].replace("_", "\\_") + " & ");
				if (cyc < cycles-1) { 
					for (int j = cyc*numberofalg; j < (cyc+1)*numberofalg ; j++) {
						if (j == bestIndex) {
							os.write("\\cellcolor{gray95}");
						}
						if (j == secondBestIndex) {
							os.write("\\cellcolor{gray25}");
						}
						if(j<(cyc+1)*numberofalg -1 ) {
							m = String.format(Locale.ENGLISH, "%.4e", median[indicator][i][j]);	
							os.write("$" + m + "$ $ $ & ");
						} else {
							m = String.format(Locale.ENGLISH, "%.4e", median[indicator][i][j]);					
							os.write("$" + m + "$ $ $\\\\" + "\n");
						}
						
					}
					
				///////---------------------This is the most important part-------------------------------*/
				}else {
					for (int j = cyc*numberofalg; j < (cyc+1)*numberofalg-1; j++) {
						if (j == bestIndex) {
							os.write("\\cellcolor{gray95}");
						}
						if (j == secondBestIndex) {
							os.write("\\cellcolor{gray25}");
						}
		
						m = String.format(Locale.ENGLISH, "%.4e", median[indicator][i][j]);		
						if (j == 0) {
							os.write("$" + m + "$ & ");
						} else {
							
							String temp;
							if ("+".equalsIgnoreCase(symbols[indicator][i][j] ))
								temp = "\\bullet"; // oplus
							else if ("-".equalsIgnoreCase(symbols[indicator][i][j] )) {
								temp = "\\circ";  // ominus
							} else if ("=".equalsIgnoreCase(symbols[indicator][i][j])){
								temp = "\\ddagger"; //approx
							} else {
								temp = "Null";
							}
							os.write("$" + m + "$$" + temp + " $ & ");
						}
					}
				}//if
				
				if(cyc == cycles - 1 ){
					if (bestIndex == (algorithmNameList_.length - 1)) {
						os.write("\\cellcolor{gray95}");
					}
					if (algorithmNameList_.length - 1 == secondBestIndex) {
						os.write("\\cellcolor{gray25}");
					}
					
					m = String.format(Locale.ENGLISH, "%.4e", median[indicator][i][algorithmNameList_.length - 1]);	
					
					String temp;
					if ("+".equalsIgnoreCase(symbols[indicator][i][algorithmNameList_.length - 1] ))
						temp = "\\bullet"; //oplus
					else if ("-".equalsIgnoreCase(symbols[indicator][i][algorithmNameList_.length - 1] )) {
						temp = "\\circ";  //ominus
					} else if ("=".equalsIgnoreCase(symbols[indicator][i][algorithmNameList_.length - 1])){
						temp = "\\ddagger"; //approx
					} else {
						temp = "Null";
					}
					
					os.write("$" + m + "$$" + temp + "$ \\\\" + "\n");
				}				
				////----------------------This is the most important part-------------------------------*/
				
			} // for
			os.write("\\hline" + "\n");
        }//for
        
		//os.write("" + mean[0][problemList_.length-1][algorithmNameList_.length-1] + "\\\\"+ "\n" ) ;

//		os.write("\\hline" + "\n");
		os.write("\\end{tabular}" + "\n");
		os.write("\\end{tiny}" + "\n");
		os.write("\\end{table*}" + "\n");
		os.close();
	} // printMedian
	
	/**
	 * Pring median and IQR
	 * @param fileName
	 * @param indicator
	 * @param median
	 * @param IQR
	 * @throws IOException
	 */
	void printMedianIQRSymbols(String fileName, int indicator, double[][][] median, double[][][] IQR,String [][][] symbols) throws IOException {
		FileWriter os = new FileWriter(fileName, true);
		os.write("\\" + "\n");
		os.write("\\begin{table*}" + "\n");
		os.write("\\caption{" + indicatorList_[indicator] + ". Median and IQR}" + "\n");
		os.write("\\label{table:median." + indicatorList_[indicator] + "}" + "\n");
		os.write("\\begin{tiny}" + "\n");
		os.write("\\centering" + "\n");
		os.write("\\begin{tabular}{l");

		// calculate the number of columns
        for (String anAlgorithmNameList_ : algorithmNameList_) {
            os.write("l");
        }
		os.write("}\n");

		os.write("\\hline");
		// write table head
		int numberofalg = 0;
		final int  numberOfalgforEachrow = 11;
		int cycles = 0;
		if (algorithmNameList_.length <=numberOfalgforEachrow){
			numberofalg = algorithmNameList_.length;
			cycles = algorithmNameList_.length/numberofalg;
		} else {	
			numberofalg = numberOfalgforEachrow;
			if(algorithmNameList_.length%numberofalg==0)
				cycles = algorithmNameList_.length/numberofalg;
			else
				cycles = algorithmNameList_.length/numberofalg+1;
		}
		
        for (int cyc=0;cyc<cycles;cyc++) {
        	
        	for (int i = -1; i < numberofalg; i++) {        		
            		if(cyc*numberofalg+i==algorithmNameList_.length){
            			os.write( " \\\\ "+ "\n");
            			break;
            		}
    			if (i == -1) {
    				os.write(" & ");
    			} else if (i == (numberofalg - 1)) {
    				os.write(" " + algorithmNameList_[cyc*numberofalg+i] + "\\\\" + "\n");
    			} else {
    				os.write(" " + algorithmNameList_[cyc*numberofalg+i] + " & ");
    			}
    		}
        	os.write("\\hline" + "\n");
			String m, s;
			// write lines
			for (int i = 0; i < problemList_.length; i++) {
				// find the best value and second best value
				double bestValue       ;
				double bestValueIQR    ;
				double secondBestValue ;
				double secondBestValueIQR ;
				int bestIndex = -1 ;
				int secondBestIndex = -1 ;
				if ((Boolean) indicatorMinimize_.get(indicatorList_[indicator])) {// minimize by default
					bestValue = Double.MAX_VALUE;
					bestValueIQR = Double.MAX_VALUE;
					secondBestValue = Double.MAX_VALUE;
					secondBestValueIQR = Double.MAX_VALUE;
					for (int j = 0; j < (algorithmNameList_.length); j++) {
						if ((median[indicator][i][j] < bestValue) ||
								((median[indicator][i][j] == bestValue) && (IQR[indicator][i][j] < bestValueIQR))) {
							secondBestIndex = bestIndex ;
							secondBestValue = bestValue ;
							secondBestValueIQR = bestValueIQR ;
							bestValue = median[indicator][i][j];
							bestValueIQR = IQR[indicator][i][j];
							bestIndex = j;
						}
						else if ((median[indicator][i][j] < secondBestValue) ||
								((median[indicator][i][j] == secondBestValue) && (IQR[indicator][i][j] < secondBestValueIQR))) {
							secondBestIndex = j ;
							secondBestValue = median[indicator][i][j] ;
							secondBestValueIQR = IQR[indicator][i][j] ;
						} // else if
					} // for
				} // if
				else { // indicator to maximize e.g., the HV
					bestValue = Double.MIN_VALUE;
					bestValueIQR = Double.MIN_VALUE;
					secondBestValue = Double.MIN_VALUE;
					secondBestValueIQR = Double.MIN_VALUE;
					for (int j = 0; j < (algorithmNameList_.length); j++) {
						if ((median[indicator][i][j] > bestValue) ||
								((median[indicator][i][j] == bestValue) && (IQR[indicator][i][j] < bestValueIQR))) {
							secondBestIndex = bestIndex ;
							secondBestValue = bestValue ;
							secondBestValueIQR = bestValueIQR ;
							bestValue = median[indicator][i][j];
							bestValueIQR = IQR[indicator][i][j];
							bestIndex = j;
						}
						else if ((median[indicator][i][j] > secondBestValue) ||
								((median[indicator][i][j] == secondBestValue) && (IQR[indicator][i][j] < secondBestValueIQR))) {
							secondBestIndex = j ;
							secondBestValue = median[indicator][i][j] ;
							secondBestValueIQR = IQR[indicator][i][j] ;
						} // else if
					} // for
				} // else
	
				os.write(problemList_[i].replace("_", "\\_") + " & ");
				if (cyc<cycles-1) { 
				for (int j = cyc*numberofalg; j < (cyc+1)*numberofalg ; j++) {
					if (j == bestIndex) {
						os.write("\\cellcolor{gray95}");
					}
					if (j == secondBestIndex) {
						os.write("\\cellcolor{gray25}");
					}
					if(j<(cyc+1)*numberofalg -1 ) {
						m = String.format(Locale.ENGLISH, "%.3e", median[indicator][i][j]);
						s = String.format(Locale.ENGLISH, "%.1e", IQR[indicator][i][j]);
						os.write("$" + m + "~(" + s + ")$ $ $ & ");
//						os.write("" + m + "~(" + s + ") $ $ & ");
					} else {
						m = String.format(Locale.ENGLISH, "%.3e", median[indicator][i][j]);
						s = String.format(Locale.ENGLISH, "%.1e", IQR[indicator][i][j]);
//						os.write("" + m + "~(" + s + ") $ $ \\\\" + "\n");
						os.write("$" + m + "~(" + s + ")$ $ $ \\\\" + "\n");
					}
					
				}
				}else {
					for (int j = cyc*numberofalg; j < (cyc+1)*numberofalg-1; j++) {
						if (j == bestIndex) {
							os.write("\\cellcolor{gray95}");
						}
						if (j == secondBestIndex) {
							os.write("\\cellcolor{gray25}");
						}
		
						m = String.format(Locale.ENGLISH, "%.3e", median[indicator][i][j]);
						s = String.format(Locale.ENGLISH, "%.1e", IQR[indicator][i][j]);
						
						if (j == 0) {
							os.write("$" + m + "~(" + s + ")$ & ");
//							os.write("" + m + "~(" + s + ")  & ");
						} else {
							
							String temp;
							if ("+".equalsIgnoreCase(symbols[indicator][i][j] ))
//								temp = "\\oplus";
								temp = "\\bullet";
							else if ("-".equalsIgnoreCase(symbols[indicator][i][j] )) {
//								temp = "\\ominus";
								temp = "\\circ";
							} else if ("=".equalsIgnoreCase(symbols[indicator][i][j])){
//								temp = "\\approx";
								temp = "\\ddagger";
							} else {
								temp = "Null";
							}
							os.write("$" + m + "~(" + s + ")$" + "$" + temp + " $ & ");
//							os.write("" + m + "~(" + s + ")" + "$" + temp + "$ & ");
						}
						
					}
				}//if
				if(cyc == cycles -1 ){
					if (bestIndex == (algorithmNameList_.length - 1)) {
						os.write("\\cellcolor{gray95}");
					}
					if (secondBestIndex == (algorithmNameList_.length - 1)) {
						os.write("\\cellcolor{gray25}");
					}
					m = String.format(Locale.ENGLISH, "%.3e", median[indicator][i][algorithmNameList_.length - 1]);
					s = String.format(Locale.ENGLISH, "%.1e", IQR[indicator][i][algorithmNameList_.length - 1]);
					
					String temp;
					if ("+".equalsIgnoreCase(symbols[indicator][i][algorithmNameList_.length - 1] ))
//						temp = "\\oplus";
						temp = "\\bullet";
					else if ("-".equalsIgnoreCase(symbols[indicator][i][algorithmNameList_.length - 1] )) {
//						temp = "\\ominus";
						temp = "\\circ";
					} else if ("=".equalsIgnoreCase(symbols[indicator][i][algorithmNameList_.length - 1])){
//						temp = "\\approx";
						temp = "\\ddagger";
					} else {
						temp = "Null";
					}
					
					os.write("$" + m + "~(" + s + ")$$" + temp + "$ \\\\" + "\n");
//					os.write("" + m + "~(" + s + ")$" + temp + "$ \\\\" + "\n");
				}
			} // for
			os.write("\\hline" + "\n");
        }//for

//		os.write("\\hline" + "\n");
		os.write("\\end{tabular}" + "\n");
		os.write("\\end{tiny}" + "\n");
		os.write("\\end{table*}" + "\n");
		os.close();
	} // printMedianIQR
	
	/**
	 * Pring mean and standard deviation
	 * @param fileName
	 * @param indicator
	 * @param median, that is mean
	 * @param IQR, that is std
	 * @throws IOException
	 */
	void printMeanStdSymbols(String fileName, int indicator, double[][][] median, double[][][] IQR,String [][][] symbols) throws IOException {
		FileWriter os = new FileWriter(fileName, true);
		os.write("\\" + "\n");
		os.write("\\begin{table*}" + "\n");
		os.write("\\caption{" + indicatorList_[indicator] + ". Mean and standard deviation}" + "\n");
		os.write("\\label{table:median." + indicatorList_[indicator] + "}" + "\n");
		os.write("\\begin{tiny}" + "\n");
		os.write("\\centering" + "\n");
		os.write("\\begin{tabular}{l");

		// calculate the number of columns
        for (String anAlgorithmNameList_ : algorithmNameList_) {
            os.write("l");
        }
		os.write("}\n");

		os.write("\\hline");
		// write table head
		int numberofalg = 0;
		final int  numberOfalgforEachrow = 11;
		int cycles = 0;
		if (algorithmNameList_.length <=numberOfalgforEachrow){
			numberofalg = algorithmNameList_.length;
			cycles = algorithmNameList_.length/numberofalg;
		} else {	
			numberofalg = numberOfalgforEachrow;
			if(algorithmNameList_.length%numberofalg==0)
				cycles = algorithmNameList_.length/numberofalg;
			else
				cycles = algorithmNameList_.length/numberofalg+1;
		}
		
        for (int cyc=0;cyc<cycles;cyc++) {
        	
        	for (int i = -1; i < numberofalg; i++) {        		
            		if(cyc*numberofalg+i==algorithmNameList_.length){
            			os.write( " \\\\ "+ "\n");
            			break;
            		}
    			if (i == -1) {
    				os.write(" & ");
    			} else if (i == (numberofalg - 1)) {
    				os.write(" " + algorithmNameList_[cyc*numberofalg+i] + "\\\\" + "\n");
    			} else {
    				os.write(" " + algorithmNameList_[cyc*numberofalg+i] + " & ");
    			}
    		}
        	os.write("\\hline" + "\n");
			String m, s;
			// write lines
			for (int i = 0; i < problemList_.length; i++) {
				// find the best value and second best value
				double bestValue       ;
				double bestValueIQR    ;
				double secondBestValue ;
				double secondBestValueIQR ;
				int bestIndex = -1 ;
				int secondBestIndex = -1 ;
				if ((Boolean) indicatorMinimize_.get(indicatorList_[indicator])) {// minimize by default
					bestValue = Double.MAX_VALUE;
					bestValueIQR = Double.MAX_VALUE;
					secondBestValue = Double.MAX_VALUE;
					secondBestValueIQR = Double.MAX_VALUE;
					for (int j = 0; j < (algorithmNameList_.length); j++) {
						if ((median[indicator][i][j] < bestValue) ||
								((median[indicator][i][j] == bestValue) && (IQR[indicator][i][j] < bestValueIQR))) {
							secondBestIndex = bestIndex ;
							secondBestValue = bestValue ;
							secondBestValueIQR = bestValueIQR ;
							bestValue = median[indicator][i][j];
							bestValueIQR = IQR[indicator][i][j];
							bestIndex = j;
						}
						else if ((median[indicator][i][j] < secondBestValue) ||
								((median[indicator][i][j] == secondBestValue) && (IQR[indicator][i][j] < secondBestValueIQR))) {
							secondBestIndex = j ;
							secondBestValue = median[indicator][i][j] ;
							secondBestValueIQR = IQR[indicator][i][j] ;
						} // else if
					} // for
				} // if
				else { // indicator to maximize e.g., the HV
					bestValue = Double.MIN_VALUE;
					bestValueIQR = Double.MIN_VALUE;
					secondBestValue = Double.MIN_VALUE;
					secondBestValueIQR = Double.MIN_VALUE;
					for (int j = 0; j < (algorithmNameList_.length); j++) {
						if ((median[indicator][i][j] > bestValue) ||
								((median[indicator][i][j] == bestValue) && (IQR[indicator][i][j] < bestValueIQR))) {
							secondBestIndex = bestIndex ;
							secondBestValue = bestValue ;
							secondBestValueIQR = bestValueIQR ;
							bestValue = median[indicator][i][j];
							bestValueIQR = IQR[indicator][i][j];
							bestIndex = j;
						}
						else if ((median[indicator][i][j] > secondBestValue) ||
								((median[indicator][i][j] == secondBestValue) && (IQR[indicator][i][j] < secondBestValueIQR))) {
							secondBestIndex = j ;
							secondBestValue = median[indicator][i][j] ;
							secondBestValueIQR = IQR[indicator][i][j] ;
						} // else if
					} // for
				} // else
	
				os.write(problemList_[i].replace("_", "\\_") + " & ");
				if (cyc<cycles-1) { 
				for (int j = cyc*numberofalg; j < (cyc+1)*numberofalg ; j++) {
					if (j == bestIndex) {
						os.write("\\cellcolor{gray95}");
					}
					if (j == secondBestIndex) {
						os.write("\\cellcolor{gray25}");
					}
					if(j<(cyc+1)*numberofalg -1 ) {
						m = String.format(Locale.ENGLISH, "%.3e", median[indicator][i][j]);
						s = String.format(Locale.ENGLISH, "%.1e", IQR[indicator][i][j]);
						os.write("$" + m + "~(" + s + ")$ $ $ & ");
//						os.write("" + m + "~(" + s + ") $ $ & ");
					} else {
						m = String.format(Locale.ENGLISH, "%.3e", median[indicator][i][j]);
						s = String.format(Locale.ENGLISH, "%.1e", IQR[indicator][i][j]);
//						os.write("" + m + "~(" + s + ") $ $ \\\\" + "\n");
						os.write("$" + m + "~(" + s + ")$ $ $ \\\\" + "\n");
					}
					
				}
				}else {
					for (int j = cyc*numberofalg; j < (cyc+1)*numberofalg-1; j++) {
						if (j == bestIndex) {
							os.write("\\cellcolor{gray95}");
						}
						if (j == secondBestIndex) {
							os.write("\\cellcolor{gray25}");
						}
		
						m = String.format(Locale.ENGLISH, "%.3e", median[indicator][i][j]);
						s = String.format(Locale.ENGLISH, "%.1e", IQR[indicator][i][j]);
						
						if (j == 0) {
							os.write("$" + m + "~(" + s + ")$ & ");
//							os.write("" + m + "~(" + s + ")  & ");
						} else {
							
							String temp;
							if ("+".equalsIgnoreCase(symbols[indicator][i][j] ))
//								temp = "\\oplus";
								temp = "\\bullet";
							else if ("-".equalsIgnoreCase(symbols[indicator][i][j] )) {
//								temp = "\\ominus";
								temp = "\\circ";
							} else if ("=".equalsIgnoreCase(symbols[indicator][i][j])){
//								temp = "\\approx";
								temp = "\\ddagger";
							} else {
								temp = "Null";
							}
							os.write("$" + m + "~(" + s + ")$" + "$" + temp + " $ & ");
//							os.write("" + m + "~(" + s + ")" + "$" + temp + "$ & ");
						}
						
					}
				}//if
				if(cyc == cycles -1 ){
					if (bestIndex == (algorithmNameList_.length - 1)) {
						os.write("\\cellcolor{gray95}");
					}
					if (secondBestIndex == (algorithmNameList_.length - 1)) {
						os.write("\\cellcolor{gray25}");
					}
					m = String.format(Locale.ENGLISH, "%.3e", median[indicator][i][algorithmNameList_.length - 1]);
					s = String.format(Locale.ENGLISH, "%.1e", IQR[indicator][i][algorithmNameList_.length - 1]);
					
					String temp;
					if ("+".equalsIgnoreCase(symbols[indicator][i][algorithmNameList_.length - 1] ))
//						temp = "\\oplus";
						temp = "\\bullet";
					else if ("-".equalsIgnoreCase(symbols[indicator][i][algorithmNameList_.length - 1] )) {
//						temp = "\\ominus";
						temp = "\\circ";
					} else if ("=".equalsIgnoreCase(symbols[indicator][i][algorithmNameList_.length - 1])){
//						temp = "\\approx";
						temp = "\\ddagger";
					} else {
						temp = "Null";
					}
					
					os.write("$" + m + "~(" + s + ")$$" + temp + "$ \\\\" + "\n");
//					os.write("" + m + "~(" + s + ")$" + temp + "$ \\\\" + "\n");
				}
			} // for
			os.write("\\hline" + "\n");
        }//for

//		os.write("\\hline" + "\n");
		os.write("\\end{tabular}" + "\n");
		os.write("\\end{tiny}" + "\n");
		os.write("\\end{table*}" + "\n");
		os.close();
	} // printMeanStd
	
	/**
	 * Invoking the generateScripts method on the RBoxplot class
	 * @param rows
	 * @param cols
	 * @param problems
	 * @param prefix
	 * @param notch
	 * @param experiment
	 * @throws IOException 
	 * @throws FileNotFoundException 
	 */
	public void generateRBoxplotScripts(int rows,
			int cols,
			String[] problems,
			String prefix,
			boolean notch,
			Experiment experiment) throws FileNotFoundException, IOException {
		RBoxplot.generateScripts(rows, cols, problems, prefix, notch, this) ;
	} // generateRBoxplotScripts

	/**
	 * Invoking the generateScripts method on the RWilcoxon class
	 * @param problems
	 * @param prefix
	 * @param experiment
	 * @throws FileNotFoundException
	 * @throws IOException
	 */
  public void generateRWilcoxonScripts(
          String[] problems,
          String prefix,
          Experiment experiment) throws FileNotFoundException, IOException {
		RWilcoxon.generateScripts(problems, prefix, this) ;
	} // generateRWilcoxonScripts

	// Inicio modificación planificación Threads
	/**
	 * 
	 * @return
	 */
	public synchronized int[] getNextProblem(){
		int[] res = new int[3];

		int alg = this.algorithmIndex;
		int runs = this.irunIndex;
		int prob = this.problemIndex;

		if(this.problemList_.length == 1){
			prob = 0;
		}
		if(this.algorithmNameList_.length == 1){
			alg = 0;
		}
				
		if(this.independentRuns_ == 1 ){
			runs = 0;			
		} 

		if(this.problemIndex < this.problemList_.length-1){
			this.problemIndex++;
		}else{
			if(this.algorithmIndex < this.algorithmNameList_.length-1){
				this.algorithmIndex++;
				this.problemIndex = 0;
			}else{
				if(this.irunIndex < this.independentRuns_-1){
					this.irunIndex++;
					this.problemIndex = 0;
					this.algorithmIndex = 0;
				}else{
					this.finished_ = true;				
				}
			}
		}

		//System.out.println("Prob = " + prob + " Alg = " + alg + " Run = " + runs);

		res[0] = prob;
		res[1] = alg;
		res[2] = runs;

		return res;
	}// getNextProblem
	// Fin modificación planificación Threads
}  // Experiment

