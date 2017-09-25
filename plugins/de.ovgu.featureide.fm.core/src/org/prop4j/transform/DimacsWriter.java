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
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;

/**
 * Transforms instances of {@link Node} into DIMACS CNF file format.
 *
 * @author Timo G&uuml;nther
 */
public class DimacsWriter {

	/** Token leading a (single-line) comment. */
	private static final String COMMENT = "c";
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

	/** Whether the writer should write a variable directory listing the names of the variables. */
	private boolean writingVariableDirectory = false;

	/**
	 * Constructs a new instance of this class with the given CNF.
	 *
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
		clauses = cnf instanceof And ? Arrays.asList(cnf.getChildren()) : Collections.singletonList(cnf);
		variableIndexes = new LinkedHashMap<>();
		for (final Object variable : cnf.getUniqueVariables()) {
			addVariable(variable);
		}
	}

	/**
	 * Adds the given variable. This means assigning an index to it.
	 *
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
	 * <p> Sets the writing variable directory flag. If true, the writer will write a variable directory at the start of the output. This is a set of comments
	 * naming the variables. This can later be used during reading so the variables are not just numbers. </p>
	 *
	 * <p> Defaults to false. </p>
	 *
	 * @param writingVariableDirectory whether to write the variable directory
	 */
	public void setWritingVariableDirectory(boolean writingVariableDirectory) {
		this.writingVariableDirectory = writingVariableDirectory;
	}

	/**
	 * Writes the DIMACS CNF file format.
	 *
	 * @return the transformed CNF; not null
	 */
	public String write() {
		String s = "";
		if (writingVariableDirectory) {
			s += writeVariableDirectory();
		}
		s += writeProblem();
		s += writeClauses();
		return s;
	}

	/**
	 * Writes the variable directory.
	 *
	 * @return the variable directory; not null
	 */
	private String writeVariableDirectory() {
		String s = "";
		for (final Entry<Object, Integer> e : variableIndexes.entrySet()) {
			s += writeVariableDirectoryEntry(e.getKey(), e.getValue());
		}
		return s;
	}

	/**
	 * Writes an entry of the variable directory.
	 *
	 * @param variable variable to list in the entry
	 * @param index index of the variable
	 * @return an entry of the variable directory; not null
	 */
	private String writeVariableDirectoryEntry(Object variable, int index) {
		return String.format("%s %d %s%n", COMMENT, index, String.valueOf(variable));
	}

	/**
	 * Writes the problem description.
	 *
	 * @return the problem description; not null
	 */
	private String writeProblem() {
		return String.format("%s %s %d %d%n", PROBLEM, CNF, variableIndexes.size(), clauses.size());
	}

	/**
	 * Writes all clauses.
	 *
	 * @return all transformed clauses; not null
	 */
	private String writeClauses() {
		String s = "";
		for (final Node clause : clauses) {
			s += writeClause(clause);
		}
		return s;
	}

	/**
	 * Writes the given clause.
	 *
	 * @param clause clause to transform; not null
	 * @return the transformed clause; not null
	 */
	private String writeClause(Node clause) {
		String s = "";
		for (final Literal l : clause.getUniqueLiterals()) {
			s += writeLiteral(l) + " ";
		}
		s += CLAUSE_END;
		s += System.lineSeparator();
		return s;
	}

	/**
	 * Writes the given literal.
	 *
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
