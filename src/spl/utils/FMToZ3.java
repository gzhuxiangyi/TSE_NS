/*
 * Creator: Jia Hui Liang 
 * Date : April 2016
 * 
 * Modifier: Jianmei Guo
 * Date: May 2016
 * 
 */

package spl.utils;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.Reader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Random;

import jmetal.encodings.variable.Binary;
import spl.fm.Product;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Global;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.Model;
import com.microsoft.z3.Params;
import com.microsoft.z3.RealExpr;
import com.microsoft.z3.Solver;

public class FMToZ3 {

    private final Context ctx;
    private final Solver solver;
    private BoolExpr[] vars = null;
    private RealExpr total_cost = null;
    private IntExpr total_used_before = null;
    private IntExpr total_defect = null;
    private IntExpr total_selected = null; // the currently selected variables
    private IntExpr total_different = null; // the number of different variables
    
    public FMToZ3() {
        HashMap<String, String> cfg = new HashMap<>();
        cfg.put("model", "true");
        cfg.put("auto-config", "false");
        
        Random randomGenerator = new Random();
        int randomInt = randomGenerator.nextInt(500000000);
        Global.setParameter("smt.random_seed", Integer.toString(randomInt));// 随机化种子
        Global.setParameter("smt.phase_selection", "5");
        this.ctx = new Context(cfg);
        this.solver = ctx.mkSolver();
    }

    public void parseDimacs(Reader dimacs) throws IOException {
        BufferedReader in = new BufferedReader(dimacs);
        String line;

        while ((line = in.readLine()) != null) {
            line = line.trim();
            if (line.startsWith("c ") || line.isEmpty()) {
                continue;
            } else if (line.startsWith("p cnf ")) {
                int numVars = Integer.parseInt(line.split("\\s+")[2]); // 运用正则表达式中的空白（通过空格、制表符）进行拆分
                vars = new BoolExpr[numVars]; // 声明变量
                for (int i = 0; i < vars.length; i++) {
                    vars[i] = ctx.mkBoolConst(Integer.toString(i + 1)); // 创建Bool常量,相当于为每个变量命名
                }
            } else { // 读取约束
                String[] clauseLine = line.split("\\s+");
                if (!clauseLine[clauseLine.length - 1].equals("0")) {
                    throw new IOException("Expected line to end with 0");
                }
                BoolExpr[] clauseLits = new BoolExpr[clauseLine.length - 1];
                for (int i = 0; i < clauseLits.length; i++) {
                    int lit = Integer.parseInt(clauseLine[i]);
                    BoolExpr var = vars[Math.abs(lit) - 1];
                    clauseLits[i] = lit > 0 ? var : ctx.mkNot(var);
                }
                solver.add(ctx.mkOr(clauseLits));
            }
        }
    }

    public void parseMandatory(Reader mandatory) throws IOException {
        BufferedReader in = new BufferedReader(mandatory);
        String line;

        while ((line = in.readLine()) != null) {
            line = line.trim();

            if (!line.isEmpty()) {
                int var = Math.abs(Integer.parseInt(line));
                solver.add(vars[var - 1]);
            }
        }
    }

    public void parseDead(Reader dead) throws IOException {
        BufferedReader in = new BufferedReader(dead);
        String line;

        while ((line = in.readLine()) != null) {
            line = line.trim();

            if (!line.isEmpty()) {
                int var = Math.abs(Integer.parseInt(line));
                solver.add(ctx.mkNot(vars[var - 1]));
            }
        }
    }

    public void parseAugment(Reader augment) throws IOException {
        BufferedReader in = new BufferedReader(augment);
        String line;

        List<RealExpr> costs = new ArrayList<>();
        List<IntExpr> used_befores = new ArrayList<>();
        List<IntExpr> defects = new ArrayList<>();

        while ((line = in.readLine()) != null) {
            line = line.trim();
            if (line.startsWith("#") || line.isEmpty()) {
                continue;
            } else {
                String[] objectiveLine = line.split("\\s+");
                BoolExpr var = vars[Integer.parseInt(objectiveLine[0]) - 1];//找到相应的变量
                
                costs.add((RealExpr) ctx.mkITE(var, ctx.mkReal(objectiveLine[1]), ctx.mkReal(0))); //if-then-else (ITE)
                used_befores.add((IntExpr) ctx.mkITE(var, ctx.mkInt(objectiveLine[2]), ctx.mkInt(0)));
                int used_before = Integer.parseInt( objectiveLine[2].trim() );
                if ( used_before == 1 ){
                	defects.add((IntExpr) ctx.mkITE(var, ctx.mkInt(objectiveLine[3]), ctx.mkInt(0)));
                }
            }
        }
    
        total_cost = (RealExpr) ctx.mkAdd(costs.toArray(new ArithExpr[]{}));
        total_used_before = (IntExpr) ctx.mkAdd(used_befores.toArray(new ArithExpr[]{}));
        total_defect = (IntExpr) ctx.mkAdd(defects.toArray(new ArithExpr[]{}));
    }

    /**
     * 
     * @throws IOException
     */
    public void parseAugment () throws IOException {
             
    	  List<IntExpr> selected = new ArrayList<>();
    	  
    	  for (int i = 0; i <vars.length; i++) {
    		  BoolExpr var = vars[i];//
    		  selected.add((IntExpr) ctx.mkITE(var, ctx.mkInt(1), ctx.mkInt(0)));
    	  }  
            
        total_selected = (IntExpr) ctx.mkAdd(selected.toArray(new ArithExpr[]{}));

    }
    // general SMT solving
    
    /**
     * 
     * @throws IOException
     */
    public void parseDifference (Product prod) {
             
    	  List<IntExpr> different = new ArrayList<>();
    	  
    	  for (int i = 0; i <vars.length; i++) {
    		  BoolExpr var = vars[i];//
    		
    		 if (prod.contains(i+1)) {
    			 different.add((IntExpr) ctx.mkITE(var, ctx.mkInt(0), ctx.mkInt(1)));
    		 } 
    		 
    		 if (prod.contains(-(i+1))) {
    			 different.add((IntExpr) ctx.mkITE(var, ctx.mkInt(1), ctx.mkInt(0)));
    		 }
    		     		  
    	  }  
            
        total_different = (IntExpr) ctx.mkAdd(different.toArray(new ArithExpr[]{}));

    }
    // general SMT solving
    
    public Binary solve() {
        solver.push();
        try {
            Random randomGenerator = new Random();
            int randomInt = randomGenerator.nextInt(500000000);
            Global.setParameter("smt.random_seed", Integer.toString(randomInt));
        	Params p = ctx.mkParams();
        	// timeout 6000ms
        	p.add("timeout", 6000);
        	solver.setParameters(p);
        
            switch (solver.check()) {
                case SATISFIABLE:
                    Model m = solver.getModel();
                    Binary b = new Binary(vars.length);
                    for (int i = 0; i < vars.length; i++) {
                        switch (m.evaluate(vars[i], false).getBoolValue()) {
                            case Z3_L_FALSE:
                                b.setIth(i, false);
                                break;
                            case Z3_L_TRUE:
                                b.setIth(i, true);
                                break;
                            case Z3_L_UNDEF:
                                b.setIth(i, System.currentTimeMillis() % 2 == 0);
                                break;
                            default:
                                throw new IllegalStateException();
                        }
                    }
                    return b;
                default:
                    return null;
            }
        } finally {
            solver.pop();
        }
    }
    
    
    // Improved search for SMTIBEAv3    
    public Binary solveBetterGIA(double totalCost, int totalUsedBefore, int totalDefect) {
        solver.push();
        try {
        	
        	solver.add(ctx.mkLe(total_cost, ctx.mkReal(Double.toString(totalCost))),
					   ctx.mkLe(total_defect, ctx.mkReal(totalDefect)) );
        	
        	Params p = ctx.mkParams();
        	p.add("timeout", 6000);
        	solver.setParameters(p);
        	
            switch (solver.check()) {
                case SATISFIABLE:
                    Model m = solver.getModel();
                    Binary b = new Binary(vars.length);
                    for (int i = 0; i < vars.length; i++) {
                        switch (m.evaluate(vars[i], false).getBoolValue()) {
                            case Z3_L_FALSE:
                                b.setIth(i, false);
                                break;
                            case Z3_L_TRUE:
                                b.setIth(i, true);
                                break;
                            case Z3_L_UNDEF:
                                b.setIth(i, System.currentTimeMillis() % 2 == 0);
                                break;
                            default:
                                throw new IllegalStateException();
                        }
                    }
                    return b;
                default:
                    return null;
            }
        } finally {
            solver.pop();
        }
    }
    
    // Solve with exactly d features
    public Binary solveWithD(int d) {
        solver.push();
        try {
                	
//        	System.out.println("d= " + d);
        	solver.add(ctx.mkLe(total_selected, ctx.mkInt(d))); // total_selected <=d
        	solver.add(ctx.mkGe(total_selected, ctx.mkInt(d)));  // d<=total_selected

        	Params p = ctx.mkParams();
        	p.add("timeout", 6000);
        	solver.setParameters(p);
        	
            switch (solver.check()) {
                case SATISFIABLE:
                    Model m = solver.getModel();
                    Binary b = new Binary(vars.length);
                    for (int i = 0; i < vars.length; i++) {
                        switch (m.evaluate(vars[i], false).getBoolValue()) {
                            case Z3_L_FALSE:
                                b.setIth(i, false);
                                break;
                            case Z3_L_TRUE:
                                b.setIth(i, true);
                                break;
                            case Z3_L_UNDEF:
                                b.setIth(i, System.currentTimeMillis() % 2 == 0);
                                break;
                            default:
                                throw new IllegalStateException();
                        }
                    }
                    return b;
                default:
                    return null;
            }
        } finally {
            solver.pop();
        }
    }
    
    // Solve a solutions that is different from existing prod with at least  d features
    public Binary solveDifferentWithD(Product prod, int d) {
        solver.push();
        try {
                	
        	parseDifference(prod);
//        	System.out.println("d= " + d);        	
        	solver.add(ctx.mkGe(total_different, ctx.mkInt(d)));  // total difference >= d
//        	solver.add(ctx.mkLe(total_different, ctx.mkInt(d)));  // total difference >= d
        	
        	Params p = ctx.mkParams();
        	p.add("timeout", 6000);
        	solver.setParameters(p);
        	
            switch (solver.check()) {
                case SATISFIABLE:
                    Model m = solver.getModel();
                    Binary b = new Binary(vars.length);
                    for (int i = 0; i < vars.length; i++) {
                        switch (m.evaluate(vars[i], false).getBoolValue()) {
                            case Z3_L_FALSE:
                                b.setIth(i, false);
                                break;
                            case Z3_L_TRUE:
                                b.setIth(i, true);
                                break;
                            case Z3_L_UNDEF:
                                b.setIth(i, System.currentTimeMillis() % 2 == 0);
                                break;
                            default:
                                throw new IllegalStateException();
                        }
                    }
                    return b;
                default:
                    return null;
            }
        } finally {
            solver.pop();
        }
    }
}
