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
package org.prop4j.transform;

import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.prop4j.Literal;
import org.prop4j.Node;

/**
 * Transforms instances of {@link Node} into DIMACS CNF file format.
 * 
 * @author Timo Guenther
 */
public class DimacsWriter {
	/** Token leading the problem definition. */
	private static final String PROBLEM = "p";
	/** Token identifying the problem type as CNF. */
	private static final String CNF = "cnf";
	/** Token denoting the end of a clause. */
	private static final String CLAUSE_END = "0";
	
	/** The clauses of the CNF to transform. */
	private final List<Node> clauses;
	/** Maps variables to indexes. */
	private final Map<Object, Integer> variableIndexes;
	
	/**
	 * Constructs a new instance of this class with the given CNF.
	 * @param cnf the CNF to transform; not null
	 * @throws IllegalArgumentException if the input is null or not in CNF
	 */
	public DimacsWriter(Node cnf) throws IllegalArgumentException {
		if (cnf == null) {
			throw new IllegalArgumentException("CNF is null");
		}
		if (!cnf.isConjunctiveNormalForm()) {
			throw new IllegalArgumentException("Input is not in CNF");
		}
		this.clauses = Arrays.asList(cnf.getChildren());
		this.variableIndexes = new LinkedHashMap<>();
		for (final Node clause : clauses) {
			for (final Literal l : clause.getLiterals()) {
				addVariable(l.var);
			}
		}
	}
	
	/**
	 * Adds the given variable.
	 * This means assigning an index to it.
	 * @param l variable to add; not null
	 */
	private void addVariable(Object variable) {
		if (variableIndexes.containsKey(variable)) {
			return;
		}
		final int index = variableIndexes.size() + 1;
		variableIndexes.put(variable, index);
	}
	
	/**
	 * Writes the DIMACS CNF file format.
	 * @return the transformed CNF; not null
	 */
	public String write() {
		String s = writeProblem();
		s += System.lineSeparator();
		for (final Node clause : clauses) {
			s += writeClause(clause);
			s += System.lineSeparator();
		}
		return s;
	}
	
	/**
	 * Writes the problem description.
	 * @return the problem description; not null
	 */
	private String writeProblem() {
		return String.format("%s %s %d %d",
				PROBLEM,
				CNF,
				variableIndexes.size(),
				clauses.size());
	}
	
	/**
	 * Writes the given clause.
	 * @param clause clause to transform; not null
	 * @return the transformed clause; not null
	 */
	private String writeClause(Node clause) {
		String s = "";
		for (final Literal l : clause.getLiterals()) {
			s += writeLiteral(l) + " ";
		}
		s += CLAUSE_END;
		return s;
	}
	
	/**
	 * Writes the given literal.
	 * @param l literal to transform; not null
	 * @return the transformed literal; not null
	 */
	private String writeLiteral(Literal l) {
		int index = variableIndexes.get(l.var);
		if (!l.positive) {
			index = -index;
		}
		return String.valueOf(index);
	}
}