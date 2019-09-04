/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.analysis.cnf;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet.Order;
import de.ovgu.featureide.fm.core.functional.Functional;

/**
 * Variables of a {@link CNF}.
 *
 * @author Sebastian Krieter
 */
public class Variables implements Serializable, IVariables, IInternalVariables {

	private static final long serialVersionUID = -1767212780361483105L;

	protected final String[] intToVar;
	protected final Map<String, Integer> varToInt;

	public Variables() {
		intToVar = new String[0];
		varToInt = Collections.emptyMap();
	}

	public Variables(Collection<String> varNameList) {
		intToVar = new String[varNameList.size() + 1];
		varToInt = new LinkedHashMap<>((int) (1.5 * varNameList.size()));

		int index = 0;
		for (final String feature : varNameList) {
			final String name = feature.toString();
			if (name == null) {
				throw new RuntimeException();
			}
			varToInt.put(name, ++index);
			intToVar[index] = name;
		}
	}

	protected Variables(Variables oldSatMapping) {
		intToVar = Arrays.copyOf(oldSatMapping.intToVar, oldSatMapping.intToVar.length);
		varToInt = new LinkedHashMap<>(oldSatMapping.varToInt);
	}

	@Override
	public List<String> convertToString(int[] literals) {
		return convertToString(literals, true, false);
	}

	@Override
	public List<String> convertToString(int[] literals, boolean includePositive, boolean includeNegative) {
		return convertToString(literals, includePositive, includeNegative, true);
	}

	@Override
	public List<String> convertToString(LiteralSet model) {
		return convertToString(model, true, false);
	}

	@Override
	public List<String> convertToString(LiteralSet literals, boolean includePositive, boolean includeNegative) {
		return convertToString(literals, includePositive, includeNegative, true);
	}

	@Override
	public List<String> convertToString(LiteralSet literals, boolean includePositive, boolean includeNegative, boolean markNegative) {
		return convertToString(literals.getLiterals(), includePositive, includeNegative, markNegative);
	}

	@Override
	public List<String> convertToString(int[] literals, boolean includePositive, boolean includeNegative, boolean markNegative) {
		final List<String> resultList = new ArrayList<>();
		for (final int var : literals) {
			if (var > 0) {
				if (includePositive) {
					resultList.add(intToVar[Math.abs(var)]);
				}
			} else {
				if (includeNegative) {
					if (markNegative) {
						resultList.add("-" + intToVar[Math.abs(var)]);
					} else {
						resultList.add(intToVar[Math.abs(var)]);
					}
				}
			}
		}
		return resultList;
	}

	@Override
	public LiteralSet convertToVariables(Iterable<String> variableNames) {
		final Collection<String> variableNameCollection = Functional.toCollection(variableNames);
		final int[] literals = new int[variableNameCollection.size()];
		int i = 0;
		for (final String varName : variableNameCollection) {
			literals[i++] = varToInt.get(varName);
		}
		return new LiteralSet(literals);
	}

	@Override
	public LiteralSet convertToVariables(Iterable<String> variableNames, boolean sign) {
		final Collection<String> variableNameCollection = Functional.toCollection(variableNames);
		final int[] literals = new int[variableNameCollection.size()];
		int i = 0;
		for (final String varName : variableNameCollection) {
			literals[i++] = sign ? varToInt.get(varName) : -varToInt.get(varName);
		}
		return new LiteralSet(literals);
	}

	@Override
	public LiteralSet convertToLiterals(Iterable<String> variableNames, boolean includePositive, boolean includeNegative) {
		if (!includeNegative && !includePositive) {
			return new LiteralSet();
		}
		final Collection<String> variableNameCollection = Functional.toCollection(variableNames);
		final int[] literals = new int[(includeNegative && includePositive) ? 2 * variableNameCollection.size() : variableNameCollection.size()];
		int i = 0;
		for (final String varName : variableNameCollection) {
			final int var = varToInt.get(varName);
			if (includeNegative) {
				literals[i++] = -var;
			}
			if (includePositive) {
				literals[i++] = var;
			}
		}
		return new LiteralSet(literals);
	}

	@Override
	public int size() {
		return intToVar.length - 1;
	}

	@Override
	public int maxVariableID() {
		return intToVar.length - 1;
	}

	@Override
	public int getVariable(String varName) {
		final Integer var = varToInt.get(varName);
		return var == null ? 0 : var;
	}

	@Override
	public int getVariable(String varName, boolean sign) {
		return sign ? getVariable(varName) : -getVariable(varName);
	}

	@Override
	public String getName(final int x) {
		return intToVar[Math.abs(x)];
	}

	@Override
	public String[] getNames() {
		return intToVar;
	}

	@Override
	public Variables clone() {
		return new Variables(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = (prime * result) + Arrays.hashCode(intToVar);
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if ((obj == null) || (getClass() != obj.getClass())) {
			return false;
		}
		return Arrays.equals(intToVar, ((Variables) obj).intToVar);
	}

	@Override
	public boolean checkClause(LiteralSet orgClause) {
		return true;
	}

	@Override
	public LiteralSet convertToInternal(LiteralSet orgClause) {
		return orgClause;
	}

	@Override
	public int[] convertToInternal(int[] orgLiterals) {
		return orgLiterals;
	}

	@Override
	public int convertToInternal(int orgLiteral) {
		return orgLiteral;
	}

	@Override
	public LiteralSet convertToOriginal(LiteralSet internalClause) {
		return internalClause;
	}

	@Override
	public int[] convertToOriginal(int[] internalLiterals) {
		return internalLiterals;
	}

	@Override
	public int convertToOriginal(int internalLiteral) {
		return internalLiteral;
	}

	@Override
	public String toString() {
		return "Variables [" + Arrays.toString(intToVar) + "]";
	}

	@Override
	public LiteralSet getLiterals() {
		final int length = intToVar.length - 1;
		final int[] literals = new int[length << 1];
		for (int i = 0; i < length; i++) {
			literals[i] = i - length;
		}
		for (int i = length; i < literals.length; i++) {
			literals[i] = (i - length) + 1;
		}
		return new LiteralSet(literals, Order.NATURAL, false);
	}

}
