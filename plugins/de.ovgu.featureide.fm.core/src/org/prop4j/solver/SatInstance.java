/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;

/**
 * Represents an instance of a satisfiability problem in CNF.</br> Use a {@link ISatSolverProvider solver provider} or the {@link #getSolver()} method to get a
 * {@link BasicSolver solver} for this problem.
 *
 * @author Sebastian Krieter
 */
public class SatInstance {

	public static void updateModel(final int[] model1, int[] model2) {
		for (int i = 0; i < model1.length; i++) {
			final int x = model1[i];
			final int y = model2[i];
			if (x != y) {
				model1[i] = 0;
			}
		}
	}

	public static void updateModel(final int[] model1, Iterable<int[]> models) {
		for (int i = 0; i < model1.length; i++) {
			final int x = model1[i];
			for (final int[] model2 : models) {
				final int y = model2[i];
				if (x != y) {
					model1[i] = 0;
					break;
				}
			}
		}
	}

	public static int[] negateModel(int[] ar) {
		final int[] nar = Arrays.copyOf(ar, ar.length);
		for (int i = 0; i < nar.length; i++) {
			nar[i] = -nar[i];
		}
		return nar;
	}

	protected final HashMap<Object, Integer> varToInt = new HashMap<>();
	protected final Object[] intToVar;
	protected final Node cnf;

	public SatInstance(Node root, Collection<?> featureList) {
		intToVar = new Object[featureList.size() + 1];
		cnf = root;

		int index = 0;
		for (final Object feature : featureList) {
			final String name = feature.toString();
			if (name == null) {
				throw new RuntimeException();
			}
			varToInt.put(name, ++index);
			intToVar[index] = name;
		}
	}

	public SatInstance(Node root) {
		this(root, getDistinctVariableObjects(root));
	}

	public static Set<Object> getDistinctVariableObjects(Node cnf) {
		final HashSet<Object> result = new HashSet<>();
		for (final Node clause : cnf.getChildren()) {
			final Node[] literals = clause.getChildren();
			for (int i = 0; i < literals.length; i++) {
				result.add(((Literal) literals[i]).var);
			}
		}
		return result;
	}

	public List<String> convertToString(int[] model) {
		return convertToString(model, true, false);
	}

	public List<String> convertToString(int[] model, boolean includePositive, boolean includeNegative) {
		final List<String> resultList = new ArrayList<>();
		for (final int var : model) {
			if (var > 0) {
				if (includePositive) {
					resultList.add(intToVar[Math.abs(var)].toString());
				}
			} else if (var < 0) {
				if (includeNegative) {
					resultList.add("-" + intToVar[Math.abs(var)].toString());
				}
			}
		}
		return resultList;
	}

	public int[] convertToInt(Collection<Literal> literals) {
		final int[] resultList = new int[literals.size()];
		int i = 0;
		for (final Literal literal : literals) {
			final Integer varIndex = varToInt.get(literal.var);
			resultList[i++] = varIndex == null ? 0 : (literal.positive ? varIndex : -varIndex);
		}
		return resultList;
	}

	public int[] convertToInt(Literal[] literals) {
		return convertToInt(Arrays.asList(literals));
	}

	public int[] convertToInt(Node[] literals) {
		final int[] resultList = new int[literals.length];
		int i = 0;
		for (final Node node : literals) {
			final Literal literal = (Literal) node;
			final Integer varIndex = varToInt.get(literal.var);
			resultList[i++] = varIndex == null ? 0 : (literal.positive ? varIndex : -varIndex);
		}
		return resultList;
	}

	public List<Literal> convertToLiterals(int[] model) {
		final List<Literal> resultList = new ArrayList<>();
		for (final int var : model) {
			resultList.add(new Literal(intToVar[Math.abs(var)], (var > 0)));
		}
		return resultList;
	}

	public Literal convertToLiteral(int var) {
		return new Literal(intToVar[Math.abs(var)], (var > 0));
	}

	protected List<String> convertToString(IVecInt model) {
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

	public int getVariable(Literal l) {
		return varToInt.get(l.var);
	}

	public int getVariable(Object var) {
		return varToInt.get(var);
	}

	public Object getVariableObject(final int x) {
		return intToVar[Math.abs(x)];
	}

}
