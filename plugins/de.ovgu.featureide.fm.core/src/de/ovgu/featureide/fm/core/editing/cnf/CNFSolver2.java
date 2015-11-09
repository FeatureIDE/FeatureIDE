/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.core.editing.cnf;

import java.util.Collection;

import org.prop4j.SatSolver;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.editing.remove.DeprecatedClause;

/**
 * Light version of {@link SatSolver}.
 * 
 * @author Sebastian Krieter
 */
public class CNFSolver2 implements ICNFSolver {

//	private final HashMap<Object, Integer> varToInt;
	private final int[] intMap; 
	private final ISolver solver;

//	public CNFSolver2(Node cnf) {
//		varToInt = new HashMap<Object, Integer>();
//		
//		if (cnf instanceof And) {
//			for (Node clause : cnf.getChildren()) {
//				if (clause instanceof Or) {
//					for (Node literal : clause.getChildren()) {
//						final Object var = ((Literal)literal).var;
//						if (!varToInt.containsKey(var)) {
//							int index = varToInt.size() + 1;
//							varToInt.put(var, index);
//						}
//					}
//				} else {
//					final Object var = ((Literal)clause).var;
//					if (!varToInt.containsKey(var)) {
//						int index = varToInt.size() + 1;
//						varToInt.put(var, index);
//					}
//				}
//			}
//		} else if (cnf instanceof Or) {
//			for (Node literal : cnf.getChildren()) {
//				final Object var = ((Literal)literal).var;
//				if (!varToInt.containsKey(var)) {
//					int index = varToInt.size() + 1;
//					varToInt.put(var, index);
//				}
//			}
//		} else {
//			varToInt.put(((Literal)cnf).var, 1);
//		}
//
//		solver = createSolver(varToInt.size());
//		intMap = new int[varToInt.size() + 1];
//		Arrays.fill(intMap, 0);
//
//		try {
//			if (cnf instanceof And) {
//				for (Node andChild : cnf.getChildren()) {
//					if (andChild instanceof Or) {
//						final Node[] literals = andChild.getChildren();
//						int[] clause = new int[literals.length];
//						int i = 0;
//						for (Node child : literals) {
//							final Literal literal = (Literal) child;
//							clause[i++] = literal.positive ? varToInt.get(literal.var) : -varToInt.get(literal.var);
//						}
//						solver.addClause(new VecInt(clause));
//					} else {
//						final Literal literal = (Literal) andChild;
//						solver.addClause(new VecInt(new int[] {literal.positive ? varToInt.get(literal.var) : -varToInt.get(literal.var)}));
//					}
//				}
//			} else if (cnf instanceof Or) {
//				final Node[] literals = cnf.getChildren();
//				int[] clause = new int[literals.length];
//				int i = 0;
//				for (Node child : literals) {
//					final Literal literal = (Literal) child;
//					clause[i++] = literal.positive ? varToInt.get(literal.var) : -varToInt.get(literal.var);
//				}
//				solver.addClause(new VecInt(clause));
//			} else {
//				final Literal literal = (Literal) cnf;
//				solver.addClause(new VecInt(new int[] {literal.positive ? varToInt.get(literal.var) : -varToInt.get(literal.var)}));
//			}
//			
//		} catch (ContradictionException e) {
//			throw new RuntimeException(e);
//		}
//	}
	
	public CNFSolver2(Collection<? extends Clause> clauses, boolean[] removedFeatures) {
//		this.varToInt = varToInt;
		intMap = new int[removedFeatures.length];
		int c = 0;
		for (int i = 0; i < intMap.length; i++) {
			if (removedFeatures[i]) {
				c++;
			}
			intMap[i] = c;
		}
//		varToInt = new HashMap<Object, Integer>();
//		for (Clause clause : clauses) {
//			for (Literal literal : clause.getLiterals()) {
//				final Object var = literal.var;
//				if (!varToInt.containsKey(var)) {
//					int index = varToInt.size() + 1;
//					varToInt.put(var, index);
//				}
//			}
//		}

		solver = createSolver(removedFeatures.length - (c + 1));

		try {
			for (Clause node : clauses) {
				final int[] literals = node.getLiterals();
				int[] clause = new int[literals.length];
				System.arraycopy(literals, 0, clause, 0, clause.length);
				
				translate(clause);
				
//				final Literal[] literals = node.getLiterals();
//				int[] clause = new int[literals.length];
//				int i = 0;
//				for (Literal literal : literals) {
//					clause[i++] = literal.positive ? varToInt.get(literal.var) : -varToInt.get(literal.var);
//				}
				solver.addClause(new VecInt(clause));
			}
		} catch (ContradictionException e) {
			throw new RuntimeException(e);
		}
	}

	private void translate(int[] clause) {
		for (int i = 0; i < clause.length; i++) {
			final int k = clause[i];
			final int j = intMap[Math.abs(k)];
			clause[i] = k - (k > 0 ? j : - j);
		}
	}

	private ISolver createSolver(int size) {
		ISolver solver = SolverFactory.newDefault();
		solver.setTimeoutMs(1000);
		solver.newVar(size);
		return solver;
	}

	public boolean isSatisfiable(int[] literals) throws TimeoutException, UnkownLiteralException {
		final int[] unitClauses = new int[literals.length];
		System.arraycopy(literals, 0, unitClauses, 0, unitClauses.length);
		
		translate(unitClauses);
//		for (int i = 0; i < unitClauses.length; i++) {
//			unitClauses[i] = unitClauses[i] - intMap[Math.abs(unitClauses[i])];
//		}
		
//		int i = 0;
//		for (Literal literal : literals) {
//			final Integer value = varToInt.get(literal.var);
//			if (value == null) {
//				throw new UnkownLiteralException(literal);
//			}
//			unitClauses[i++] = literal.positive ? value : -value;
//		}
		return solver.isSatisfiable(new VecInt(unitClauses));
	}

//	public boolean isSatisfiable(Literal[] literals) throws TimeoutException, UnkownLiteralException {
//		final int[] unitClauses = new int[literals.length];
//		int i = 0;
//		for (Literal literal : literals) {
//			final Integer value = varToInt.get(literal.var);
//			if (value == null) {
//				throw new UnkownLiteralException(literal);
//			}
//			unitClauses[i++] = literal.positive ? value : -value;
//		}
//		return solver.isSatisfiable(new VecInt(unitClauses));
//	}

	
	public void reset() {
		solver.reset();
	}

	/**
	 * @param mainClause
	 */
	public void addClause(DeprecatedClause mainClause) {
		final int[] literals = mainClause.literals;
		final int[] unitClauses = new int[literals.length];
		System.arraycopy(literals, 0, unitClauses, 0, unitClauses.length);
		
		translate(unitClauses);
		
		try {
			solver.addClause(new VecInt(unitClauses));
		} catch (ContradictionException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}

//	/**
//	 * @return the varToInt
//	 */
//	public HashMap<Object, Integer> getVarToInt() {
//		return varToInt;
//	}

}