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
package org.prop4j.solver;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.core.Solver;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;

import de.ovgu.featureide.fm.core.FMCorePlugin;

/**
 * Represents an instance of a satisfiability problem in CNF.</br>
 * Use a {@link ISolverProvider solver provider} or the {@link #getSolver()} method
 * to get a {@link BasicSolver solver} for this problem.
 * 
 * @author Sebastian Krieter
 */
public class SatInstance implements ISolverProvider {

	public static void updateModel(final int[] model1, int[] model2) {
		for (int i = 0; i < model1.length; i++) {
			final int x = model1[i];
			final int y = model2[i];
			if (x != y) {
				model1[i] = 0;
			}
		}
	}
	
	public static int[] negateModel(int[] ar) {
		int[] nar = Arrays.copyOf(ar, ar.length);
		for (int i = 0; i < nar.length; i++) {
			nar[i] = -nar[i];
		}
		return nar;
	}

	protected final HashMap<Object, Integer> varToInt = new HashMap<>();
	protected final Object[] intToVar;
	protected final Node cnf;

	public SatInstance(Node root, List<?> featureList) {
		this.intToVar = new Object[featureList.size() + 1];
		this.cnf = root;

		int index = 0;
		for (Object feature : featureList) {
			final String name = feature.toString();
			if (name == null) {
				throw new RuntimeException();
			}
			varToInt.put(name, ++index);
			intToVar[index] = name;
		}
	}

	protected void initSolver(Solver<?> solver) {
		solver.newVar(varToInt.size());
		final Node[] cnfChildren = cnf.getChildren();
		solver.setExpectedNumberOfClauses(cnfChildren.length);
		try {
			for (Node node : cnfChildren) {
				final Node[] children = node.getChildren();
				final int[] clause = new int[children.length];
				for (int i = 0; i < children.length; i++) {
					final Literal literal = (Literal) children[i];
					clause[i] = literal.positive ? varToInt.get(literal.var) : -varToInt.get(literal.var);
				}
				solver.addClause(new VecInt(clause));
			}
		} catch (ContradictionException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	public List<String> convertToString(int[] model) {
		final List<String> resultList = new ArrayList<>(model.length);
		for (int var : model) {
			resultList.add(intToVar[Math.abs(var)].toString());
		}
		return resultList;
	}

	public List<String> convertToString(IVecInt model) {
		final List<String> resultList = new ArrayList<>(model.size());
		final IteratorInt modelIt = model.iterator();
		while (modelIt.hasNext()) {
			resultList.add(intToVar[Math.abs(modelIt.next())].toString());
		}
		return resultList;
	}

	public Node getCnf() {
		return cnf;
	}

	public int getNumberOfVariables() {
		return intToVar.length - 1;
	}

	public Literal getLiteral(final int x) {
		return new Literal(intToVar[Math.abs(x)], x > 0);
	}

	public int getSignedVariable(Literal l) {
		return l.positive ? varToInt.get(l.var) : -varToInt.get(l.var);
	}

	@Override
	public BasicSolver getSolver() {
		return new BasicSolver(this);
	}

	public int getVariable(Literal l) {
		return varToInt.get(l.var);
	}

	public Object getVariableObject(final int x) {
		return intToVar[Math.abs(x)];
	}

}
