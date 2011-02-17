package org.prop4j;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.ConstrGroup;
import org.sat4j.tools.ModelIterator;
import org.sat4j.tools.RemiUtils;
import org.sat4j.tools.SolutionCounter;

/**
 * A solver that computes if a given propositional node is satisfiable and
 * retrieves solutions.
 * 
 * @author Thomas Thüm
 */
public class SatSolver {
	
	protected boolean contradiction = false;
	
	protected HashMap<Object, Integer> varToInt;
	
	protected HashMap<Integer, Object> intToVar;

	protected ISolver solver;
	
	public SatSolver(Node node, long timeout) {
		varToInt = new HashMap<Object, Integer>();
		intToVar = new HashMap<Integer, Object>();
		readVars(node);

		initSolver(node, timeout);
	}
	
	protected void readVars(Node node) {
		if (node instanceof Literal) {
			Object var = ((Literal) node).var;
			if (!varToInt.containsKey(var)) {
				int index = varToInt.size() + 1;
				varToInt.put(var, index);
				intToVar.put(index, var);
			}
		}
		else
			for (Node child : node.getChildren())
				readVars(child);
	}
	
	protected void initSolver(Node node, long timeout) {
		solver = SolverFactory.newDefault();
        solver.setTimeoutMs(timeout);
		node = node.toCNF();
    	solver.newVar(varToInt.size());
    	addClauses(node);
	}

	public void addClauses(Node root) {
		if (contradiction)
			return;
        try {
    		if (root instanceof And)
    			for (Node node : root.getChildren())
    				addClause(node);
    		else
    			addClause(root);
        } catch (ContradictionException e) {
        	contradiction = true;
        }
	}

	protected void addClause(Node node) throws ContradictionException {
		try {
			if (node instanceof Or) {
				int[] clause = new int[node.children.length];
				int i = 0;
				for (Node child : node.getChildren())
					clause[i++] = getIntOfLiteral(child);
				solver.addClause(new VecInt(clause));
			}
			else {
				int literal = getIntOfLiteral(node);
				solver.addClause(new VecInt(new int[] {literal}));
			}
		} catch (ClassCastException e) {
			throw new RuntimeException("expression is not in cnf", e);
		}
	}

	protected int getIntOfLiteral(Node node) {
		Object var = ((Literal) node).var;
		if (!varToInt.containsKey(var)) {
			int index = varToInt.size() + 1;
			varToInt.put(var, index);
			intToVar.put(index, var);
			solver.newVar(1);
			//hack to get around an ArrayIndexOutOfBoundsException by Sat4J 2.0.5
	    	try {
				solver.addClause(new VecInt(new int[] {index, -index}));
			} catch (ContradictionException e) {
				//cannot occur
			}
			//hack end
		}
		int value = varToInt.get(var);
		value *= ((Literal) node).positive ? 1 : -1;
		return value;
	}
	
	public List<Literal> knownValues() {
		LinkedList<Literal> list = new LinkedList<Literal>();
		try {
			IVecInt bone = RemiUtils.backbone(solver);
			IteratorInt iter = bone.iterator();
			while (iter.hasNext()) {
				int value = iter.next();
				Object var = intToVar.get(Math.abs(value));
				Literal literal = new Literal(var, value > 0);
				list.add(literal);
			}
		} catch (TimeoutException e) {
			e.printStackTrace();
		} 
		return list;
	}
	
	public boolean isSatisfiable() throws TimeoutException {
		return !contradiction && solver.isSatisfiable();
	}

	public boolean isSatisfiable(Node[] literals) throws TimeoutException {
		if (contradiction)
			return false;
		int[] unitClauses = new int[literals.length];
		int i = 0;
		for (Node literal : literals)
			unitClauses[i++] = getIntOfLiteral(literal);
		return solver.isSatisfiable(new VecInt(unitClauses));
	}
	
	public boolean isSatisfiable(List<Node> literals) throws TimeoutException {
		if (contradiction)
			return false;
		int[] unitClauses = new int[literals.size()];
		int i = 0;
		for (Node literal : literals)
			unitClauses[i++] = getIntOfLiteral(literal);
		return solver.isSatisfiable(new VecInt(unitClauses));
	}
	
	public boolean isSatisfiable(Node node) throws TimeoutException {
		if (contradiction)
			return false;

		if (!(node instanceof And))
			node = new And(node);

		ConstrGroup group = new ConstrGroup();
		IVecInt unit = new VecInt();
		try {
			for (Node child : node.getChildren()) {
				if (child instanceof Or) {
					IVecInt clause = new VecInt();
					for (Node literal : child.getChildren())
						clause.push(getIntOfLiteral(literal));
					group.add(solver.addClause(clause));
				}
				else {
					unit.push(getIntOfLiteral(child));
				}
			}
		} catch (ContradictionException e) {
			group.removeFrom(solver);
			return false;
		}
		
		boolean satisfiable = solver.isSatisfiable(unit);
		group.removeFrom(solver);
		return satisfiable;
	}

	/**
	 * Counts the solutions of the propositional formula. If the given timeout
	 * is reached the result is negative.
	 * 
	 * Since -0 equals 0, the output is y = -1 - x. If the output y is negative
	 * there are at least x = -1 - y solutions. 
	 * 
	 * @return number of solutions (at least solutions)
	 */
	public long countSolutions() {
		if (contradiction)
            return 0;
		long number = 0;
		SolutionCounter counter = new SolutionCounter(solver);
        try {
        	number = counter.countSolutions();
		} catch (TimeoutException e) {
			number = -1 - counter.lowerBound();
		}
    	return number;
	}

	public String getSolutions(int number) throws TimeoutException {
		if (contradiction)
            return "contradiction\n";

		StringBuffer out = new StringBuffer();
        IProblem problem = new ModelIterator(solver);
        int[] lastModel = null;
    	for (int i = 0; i < number; i++) {
			if (!problem.isSatisfiable(i > 0)) {
				out.append("only " + i + " solutions\n");
				break;
			}
			int[] model = problem.model();
			if (lastModel != null) {
				boolean same = true;
				for (int j = 0; j < model.length; j++)
					if (model[j] != lastModel[j])
						same = false;
				if (same) {
					out.append("only " + i + " solutions\n");
					break;
				}
			}
			lastModel = model;
			StringBuilder pos = new StringBuilder();
			StringBuilder neg = new StringBuilder();
			for (int var : model)
				if (var > 0)
					pos.append(intToVar.get(Math.abs(var)) + " ");
				else
					neg.append(intToVar.get(Math.abs(var)) + " ");
			out.append("true: " + pos + "    false: " + neg + "\n");
		}
    	return out.toString();
	}

	public String getSolution() throws TimeoutException {
		if (contradiction)
            return null;

		StringBuilder out = new StringBuilder();
        IProblem problem = new ModelIterator(solver);
		if (!problem.isSatisfiable())
			return null;
		int[] model = problem.model();
		for (int var : model)
			if (var > 0)
				out.append(intToVar.get(Math.abs(var)) + "\n");
    	return out.toString();
	}

}
