/*
 * BoxPlot.java
 * 
 * The class BoxPlot is used to plot boxplots for a set of algorithms, often controlled by a newly proposed algorithm.
 * The boxplots are stored in folder :experimentName/BoxPlot/cotrolalg/
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
package spl;

import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.text.NumberFormat;

import jmetal.qualityIndicator.util.MetricsUtil;
import jmetal.util.Configuration;
import spl.utils.FileUtils;

/**
 * @author Administrator
 *
 */
public class BoxPlot {
	String experimentName_;
	String [] algNames_;
	String controlAlg_;// The control algorithm, often be the newly proposed algorithms
	String [] proNames_;
	String [] indicatorNames_;
	int numberOfRuns_;
	int t_;
	int nproducts_;
	long timeMS_;
	/**
	 * 
	 */
	public BoxPlot(String experimentName,String [] algNames,String controlAlg, String [] proNames, 
			String []indicatorNames,int numberOfRuns) {
		experimentName_ = experimentName;
		algNames_ = algNames;
		proNames_ = proNames;
		indicatorNames_ = indicatorNames;
		numberOfRuns_ = numberOfRuns;
		controlAlg_ = controlAlg;
		// TODO Auto-generated constructor stub
	}

	public BoxPlot(String experimentName,String [] algNames,String controlAlg, String [] proNames, 
			String []indicatorNames,int numberOfRuns, int t, int nproducts, long timeMS) {
		experimentName_ = experimentName;
		algNames_ = algNames;
		proNames_ = proNames;
		indicatorNames_ = indicatorNames;
		numberOfRuns_ = numberOfRuns;
		controlAlg_ = controlAlg;
		t_ = t;
		nproducts_ = nproducts;
		timeMS_ = timeMS;
		// TODO Auto-generated constructor stub
	}	
	
	
	
	public void execut(){
		MetricsUtil meticsUtil = new MetricsUtil();
		NumberFormat nf = NumberFormat.getNumberInstance();
        nf.setMaximumFractionDigits(2); 
     
		for (int k = 0;k < proNames_.length;k++){ // for each problem
			 FileUtils.CheckDir(experimentName_ + "/mBoxPlot/");    
			 String fmFileName = proNames_[k];
			 
			 String mFileName = "FM_" + fmFileName;
	         mFileName =  mFileName.replace('.', '_');
	         mFileName =  mFileName.replace('-', '_');
	         mFileName = mFileName.replace(',', '_');
	         
	         for(int j = 0;j < indicatorNames_.length; j++) {//for each indicator
	        	 
	        	 String indicator = indicatorNames_[j];
	        	 String storePath = experimentName_ + "/mBoxPlot/" + t_ + "wise/";
	        	 FileUtils.CheckDir(storePath);
	        	 
        		 storePath = storePath + mFileName + "_" + indicator + "_parameter" + algNames_[0].substring(4,algNames_[0].indexOf('=')) + "_BoxPlot.m";// 9 IS TO skip "NSprobSAT"
        		  
    	    	 FileUtils.resetFile(storePath);System.out.println(storePath); 
    	    	 
    	    	 double [][] indicatorValues = new double[numberOfRuns_][algNames_.length];	
    	    	 
    	    	 
    	    	 // Read data for each algorithm
    	    	 for(int i = 0;i < algNames_.length;i++) {//for each algorithm
    	    		 
    	    		String indicatorPath = experimentName_  + algNames_[i] + "/" +  proNames_[k] + "/"
    	    				+ t_ + "wise/" + nproducts_ + "prods/"+ timeMS_ + "ms/" + indicatorNames_[j];
    	    		
 					System.out.println(indicatorPath);
 					double [][] values = meticsUtil.readFront(indicatorPath);
// 					System.out.println(values.length);
 					for (int r = 0;r < numberOfRuns_;r++){
// 						System.out.println(values[r][0]);
 						indicatorValues[r][i] = values[r][0];
 					}//for r					
 					
    	    	 } // for i
    	    	 
    	    	 try {
    				 /* Open the file */
    			      FileOutputStream fos   = new FileOutputStream(storePath)     ;
    			      OutputStreamWriter osw = new OutputStreamWriter(fos)    ;
    			      BufferedWriter bw      = new BufferedWriter(osw)        ;
    			      
    			      bw.write("clear ");
    			      bw.newLine();
    			      bw.write("clc ");
    			      bw.newLine();
    			      bw.write("set(gca,'NextPlot','add','Box','on','Fontname','Times New Roman','FontSize',25,'LineWidth',1.3);");
    			      bw.newLine();
    			      bw.write("set(gcf,'Position',[700 300 480 450]);"); bw.newLine();
    			      
    			      bw.write("indicatorValues = [ ");
    			      String strToWrite;
    			      
    			      for(int ii=0;ii < numberOfRuns_;ii++){
    			    	  strToWrite ="";
    			    	  for(int jj=0;jj < algNames_.length;jj++){
    			    		  strToWrite = strToWrite +  nf.format(indicatorValues[ii][jj]) +" ";
    			    		  
    			    		 
    			    	  }
    			    	  bw.write(strToWrite);
    			    	  bw.newLine();
    			      }
    			      bw.write("]; ");
    			      bw.newLine();    			      
    			          			      
    			      bw.write("meanValue = mean(indicatorValues);");bw.newLine();
    			      
//    			      bw.write("plot(meanValue,'LineStyle','g--','MarkerType', 'o', 'MarkerFaceColor',m,"
//    			      		+ "'linewidth',2)");bw.newLine();
    			      		
    			      bw.write("plot(meanValue,'LineStyle','-.','color','g','Marker', 'o', 'MarkerSize',7,"
    			      		+ "'MarkerFaceColor','g','MarkerEdgeColor','[0.07,0.21,0.14]','linewidth',2)");
    			      bw.newLine();
    			      		
    			      bw.write("hold on");bw.newLine();
    			    		  
    			      bw.write("h = boxplot(indicatorValues," + "'sym'"+ "," + "'r*'," + "" + "'outliersize',3" +  ",'notch','off');");
    			      bw.newLine();
    			      
    			      bw.write("set(h,'LineWidth',2.5);");  bw.newLine();
    			      
    			      bw.write(" tit = title('"+ fmFileName.substring(0, fmFileName.length() - 7) + " (t = " + t_ + ")');");
			          bw.newLine();	
			          bw.write("set(tit,'fontsize',20)");
			          bw.newLine();
    			        
    			      bw.newLine();
    			      bw.write("set(gca,'fontsize',25)");
    			      bw.newLine();
    			      String xtick = "[";
    			      String xtickLabel = "{'";
    			      for (int kk = 0; kk< algNames_.length-1;kk++ ) {
    			    	  xtick = xtick + (kk+1) + " ";
    			    	  xtickLabel = xtickLabel + algNames_[kk]+ "',' ";
    			      }
    			      xtick = xtick + algNames_.length + "]";
    			      xtickLabel = xtickLabel + algNames_[algNames_.length-1]+ "'}";
    			      bw.write("set(gca, 'XTick'," + xtick+")") ;
    			      bw.newLine();
    			      bw.write("set(gca,'XTickLabel',"+xtickLabel+")") ;
    			      bw.newLine();			      
    			      
//    			      xticklabel_rotate([1:12],60,{'dMOABC',' MOEAD',' SMPSO',' GDE3',' AbYSS',' CellDE',' IBEA',' MOCell',' OMOPSO',' NSGAII',' PAES',' SPEA2'},'interpreter','none')			      
    			      bw.write(" xl = xlabel('\\it P_r');");
    			      bw.newLine();			      
//    			      bw.write("set(xl,'fontsize',16)");
//    			      bw.newLine();
//    			      bw.write("set(gca,'XTickLabel',{'0.0','0.1','0.2','0.3','0.4','0.5','0.6','0.7','0.8','0.9','1.0'})");
    			      bw.write("set(gca,'XTickLabel',{'0.1','0.2','0.3','0.4','0.5','0.6','0.7','0.8','0.9','1.0'})");
//    			      bw.write("set(gca,'XTickLabel',{'2','10','20','30','40','50','60','70','80','90','100'})");
    			      bw.newLine();
    			      bw.write(" yl = ylabel('"+ indicatorNames_[j]+ " (%)');");
    			      bw.newLine();
    			      bw.write("set(yl,'fontsize',25)");
    			      bw.newLine();
//    			      bw.write("xticklabel_rotate(["+ "1:"+algNames_.length+"],30,"+ xtickLabel+ ",'interpreter','none')");
    			      bw.newLine();
    			      bw.write("th=rotateticklabel(gca, 90);");
    			      
    			      /* Close the file */
    			      bw.close();
    			    }catch (IOException e) {
    				      Configuration.logger_.severe("Error acceding to the file");
    				      e.printStackTrace();
    			    }//catch
    	    	 
	         } // for j  
			 
		} // for k	
		
	}
	
	/**
	 * @param args
	 */
	public static void main(String[] args) {
		    
	    String experimentName = "./outputOrderParameter/";   
	    
	    int t   = 6; // t-wise
	    int nproducts = 50; // the number of products
	    long timeMS = (long)600000 *1; // the time allowed
		  
		int numberofRuns = 10;
		
		String [] algNames = new String[]{
				
				//---------------------------------R1------------------------
//	    		 "NSR1P=0.0", "NSR1P=0.1",
//				 "NSR1P=0.2", "NSR1P=0.3", "NSR1P=0.4", "NSR1P=0.5", 
//	    		 "NSR1P=0.6","NSR1P=0.7", "NSR1P=0.8", "NSR1P=0.9", "NSR1P=1.0", 
				
				"NSR1NbRatio=0.1","NSR1NbRatio=0.2","NSR1NbRatio=0.3","NSR1NbRatio=0.4","NSR1NbRatio=0.5","NSR1NbRatio=0.6",
				"NSR1NbRatio=0.7","NSR1NbRatio=0.8","NSR1NbRatio=0.9","NSR1NbRatio=1.0",
				//---------------------------------R1 END------------------------
				
				
//	    		 "NSprobSATP=0.0", "NSprobSATP=0.1",
//				 "NSprobSATP=0.2", "NSprobSATP=0.3", "NSprobSATP=0.4", "NSprobSATP=0.5", 
//	    		 "NSprobSATP=0.6","NSprobSATP=0.7", "NSprobSATP=0.8", "NSprobSATP=0.9", "NSprobSATP=1.0", 
	    		
//	    		"NSprobSATNbr=2","NSprobSATNbr=10","NSprobSATNbr=20","NSprobSATNbr=30","NSprobSATNbr=40","NSprobSATNbr=50",
//	    		"NSprobSATNbr=60","NSprobSATNbr=70","NSprobSATNbr=80","NSprobSATNbr=90","NSprobSATNbr=100",
		};
		
		String [] problemNames = new String[]{				
//	    		"CounterStrikeSimpleFeatureModel",//24
//				"SPLSSimuelESPnP", //32
//				"DSSample", //41
//				"WebPortal",//43    
//				"Drupal", //48
//				"ElectronicDrum",//52
//				"SmartHomev2.2",//60
//				"VideoPlayer", // 71
//				"Amazon", // 79
//				"ModelTransformation", // 88
//				"CocheEcologico",//94
//				"Printers",//	172	   	
				
//				// -------------30S------------
//				"E-shop",//	290		    			
//	  			"toybox", //544
//				"axTLS", //684  
				
//				// -------------600S,15 runs------------	
				"ecos-icse11",// 1244 
				"freebsd-icse11", // 1396 
				"Automotive01", //2513 
				"SPLOT-3CNF-FM-5000-1000-0,30-SAT-1",// 5000
				"2.6.28.6-icse11", //6888
//				"Automotive02_V3",//18434, YES 
		};
		
		for (int i = 0; i < problemNames.length;i++) {
			problemNames [i] = problemNames [i] + ".dimacs";
		}
				
		
		String [] indicatorNames =new String[]{
	    		"Coverage",
				};		
		
		String controlAlg = "NSR1NbRatio=0.1";//
		
		BoxPlot boxPlot = new BoxPlot(experimentName,algNames,controlAlg,problemNames, 
				indicatorNames,numberofRuns, t, nproducts,timeMS);
		boxPlot.execut();
		// TODO Auto-generated method stub

	}

}
