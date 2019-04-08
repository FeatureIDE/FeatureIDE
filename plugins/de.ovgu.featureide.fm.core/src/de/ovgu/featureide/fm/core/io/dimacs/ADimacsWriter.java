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

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;

/**
 * Writes DIMACS format.
 *
 * @author Timo Günther
 * @author Sebastian Krieter
 */
public abstract class ADimacsWriter {

	/** Token leading a (single-line) comment. */
	protected static final String COMMENT = "c";
	/** Token leading the problem definition. */
	protected static final String PROBLEM = "p";
	/** Token identifying the problem type as CNF. */
	protected static final String CNF = "cnf";
	/** Token denoting the end of a clause. */
	protected static final String CLAUSE_END = "0";

	/** Maps variables to indexes. */
	protected final Map<Object, Integer> variableIndexes;

	/** Whether the writer should write a variable directory listing the names of the variables. */
	protected boolean writingVariableDirectory = false;

	/**
	 * Constructs a new instance of this class with the given CNF.
	 *
	 * @param cnf the CNF to transform; not null
	 * @throws IllegalArgumentException if the input is null or not in CNF
	 */
	public ADimacsWriter(Collection<?> variables) {
		variableIndexes = new LinkedHashMap<>();
		for (final Object variable : variables) {
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
		final StringBuilder sb = new StringBuilder();
		if (writingVariableDirectory) {
			writeVariableDirectory(sb);
		}
		writeProblem(sb);
		writeClauses(sb);
		return sb.toString();
	}

	/**
	 * Writes the variable directory.
	 *
	 * @param sb the string builder that builds the document
	 */
	private void writeVariableDirectory(StringBuilder sb) {
		for (final Entry<Object, Integer> e : variableIndexes.entrySet()) {
			writeVariableDirectoryEntry(sb, e.getKey(), e.getValue());
		}
	}

	/**
	 * Writes an entry of the variable directory.
	 *
	 * @param sb the string builder that builds the document
	 * @param variable variable to list in the entry
	 * @param index index of the variable
	 */
	private void writeVariableDirectoryEntry(StringBuilder sb, Object variable, int index) {
		sb.append(String.format("%s %d %s%n", COMMENT, index, String.valueOf(variable)));
	}

	/**
	 * Writes the problem description.
	 *
	 * @param sb the string builder that builds the document
	 */
	private void writeProblem(StringBuilder sb) {
		sb.append(String.format("%s %s %d %d%n", PROBLEM, CNF, variableIndexes.size(), getNumberOfClauses()));
	}

	protected abstract int getNumberOfClauses();

	/**
	 * Writes all clauses.
	 *
	 * @param sb the string builder that builds the document
	 */
	protected abstract void writeClauses(StringBuilder sb);

}
