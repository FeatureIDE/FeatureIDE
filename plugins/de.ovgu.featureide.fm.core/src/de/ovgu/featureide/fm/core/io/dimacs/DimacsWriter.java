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
package de.ovgu.featureide.fm.core.io.dimacs;

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

	/** The clauses of the CNF to transform. */
	private List<Node> clauses;
	/** Maps variables to indexes. */
	private final Map<Object, Integer> variableIndexes = new LinkedHashMap<>();

	/** Whether the writer should write a variable directory listing the names of the variables. */
	private boolean writeVariableDirectory = false;

	/**
	 * <p> Sets the writing variable directory flag. If true, the writer will write a variable directory at the start of the output. This is a set of comments
	 * naming the variables. This can later be used during reading so the variables are not just numbers. </p>
	 *
	 * <p> Defaults to false. </p>
	 *
	 * @param writeVariableDirectory whether to write the variable directory
	 */
	public void setWritingVariableDirectory(boolean writeVariableDirectory) {
		this.writeVariableDirectory = writeVariableDirectory;
	}

	/**
	 * Writes the DIMACS CNF file format.
	 *
	 * @param cnf the CNF to transform; not null
	 * @return the transformed CNF; not null
	 * @throws IllegalArgumentException if the input is null or not in CNF
	 */
	public String write(Node cnf) throws IllegalArgumentException {
		if (cnf == null) {
			throw new IllegalArgumentException("CNF is null");
		}
		if (!cnf.isConjunctiveNormalForm()) {
			throw new IllegalArgumentException("Input is not in CNF");
		}

		try {
			clauses = cnf instanceof And ? Arrays.asList(cnf.getChildren()) : Collections.singletonList(cnf);
			addVariables(cnf);

			final StringBuilder sb = new StringBuilder();
			writeVariableDirectory(sb);
			writeProblem(sb);
			writeClauses(sb);

			return sb.toString();
		} finally {
			variableIndexes.clear();
			clauses = null;
		}
	}

	/**
	 * Adds the given variable. This means assigning an index to it.
	 *
	 * @param l variable to add; not null
	 */
	private void addVariables(Node cnf) {
		// TODO make sure that variables are in same order as read
		for (final Object variable : cnf.getUniqueVariables()) {
			if (!variableIndexes.containsKey(variable)) {
				variableIndexes.put(variable, variableIndexes.size() + 1);
			}
		}
	}

	/**
	 * Writes the variable directory.
	 *
	 * @return the variable directory; not null
	 */
	private void writeVariableDirectory(StringBuilder sb) {
		if (writeVariableDirectory) {
			for (final Entry<Object, Integer> e : variableIndexes.entrySet()) {
				sb.append(DIMACSFormat.COMMENT_START);
				sb.append(e.getValue());
				sb.append(' ');
				sb.append(e.getKey());
				sb.append(System.lineSeparator());
			}
		}
	}

	/**
	 * Writes the problem description.
	 *
	 * @return the problem description; not null
	 */
	private void writeProblem(StringBuilder sb) {
		sb.append(DIMACSFormat.PROBLEM);
		sb.append(' ');
		sb.append(DIMACSFormat.CNF);
		sb.append(' ');
		sb.append(variableIndexes.size());
		sb.append(' ');
		sb.append(clauses.size());
		sb.append(System.lineSeparator());
	}

	/**
	 * Writes all clauses.
	 *
	 * @return all transformed clauses; not null
	 */
	private void writeClauses(StringBuilder sb) {
		for (final Node clause : clauses) {
			for (final Literal l : clause.getUniqueLiterals()) {
				final int index = variableIndexes.get(l.var);
				sb.append(l.positive ? index : -index);
				sb.append(' ');
			}
			sb.append(DIMACSFormat.CLAUSE_END);
			sb.append(System.lineSeparator());
		}
	}

}
