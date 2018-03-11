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

import java.io.BufferedReader;
import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.text.ParseException;
import java.util.LinkedHashMap;
import java.util.Map;

import javax.annotation.Nonnull;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;

/**
 * Transforms DIMACS CNF files into instances of {@link Node}.
 *
 * @author Timo G&uuml;nther
 */
public class DimacsReader {

	/** Maps indexes to variables. */
	private final Map<Integer, Object> indexVariables = new LinkedHashMap<>();
	/**
	 * The amount of variables as declared in the problem definition. May differ from the actual amount of variables found.
	 */
	private int variableCount;
	/** The amount of clauses in the problem. */
	private int clauseCount;
	/**
	 * True iff the last clause has been reached. In this case, the token denoting the end of a clause is optional. However, if it exists, any non-comment data
	 * past it is illegal.
	 */
	private boolean eof = false;
	/** True to read the variable directory for naming variables. */
	private boolean readVariableDirectory = false;
	/** True when currently reading the comment section at the beginning of the file and parsing variable names. */
	private boolean readingVariables;

	/**
	 * <p> Sets the reading variable directory flag. If true, the reader will look for a variable directory in the comments. This contains names for the
	 * variables which would otherwise just be numbers. </p>
	 *
	 * <p> Defaults to false. </p>
	 *
	 * @param readingVariables whether to read the variable directory
	 */
	public void setReadingVariableDirectory(boolean readVariableDirectory) {
		this.readVariableDirectory = readVariableDirectory;
	}

	/**
	 * Reads the input.
	 *
	 * @param in The source to read from.
	 * @return a CNF; not null
	 * @throws IOException if the reader encounters a problem.
	 * @throws ParseException if the input does not conform to the DIMACS CNF file format
	 */
	@Nonnull
	public Node read(Reader in) throws ParseException, IOException {
		readingVariables = readVariableDirectory;
		try (final BufferedReader reader = new BufferedReader(in)) {
			eof = false;
			readProblem(reader);
			final Node[] clauses = readClauses(reader);
			eof = true;
			if (readToken(reader) != null) {
				throw new ParseException("Trailing data", -1);
			}
			final int actualVariableCount = indexVariables.size();
			if (variableCount < actualVariableCount) {
				throw new ParseException(String.format("Found %d instead of %d variables", actualVariableCount, variableCount), -1);
			}
			return new And(clauses);
		} finally {
			indexVariables.clear();
			variableCount = -1;
			clauseCount = -1;
		}
	}

	/**
	 * Reads the next non-comment token. Also reads any comments before it.
	 *
	 * @return the next token; null if already completely read and empty
	 * @throws ParseException if there is no token left in the input but the reader is not yet done
	 * @throws IOException
	 */
	private String readToken(BufferedReader reader) throws ParseException, IOException {
		for (String line = reader.readLine(); line != null; line = reader.readLine()) {
			if (line.startsWith(DIMACSFormat.COMMENT_START)) {
				readComment(line); // read comments ...
			} else if (!line.trim().isEmpty()) {
				readingVariables = false;
				return line; // ... until a non-comment token is found.
			}
		}
		if (!eof) {
			throw new ParseException("Unexpected end of input", -1);
		}
		return null;
	}

	/**
	 * Reads the input. Calls {@link #read(Reader)}.
	 *
	 * @param in The string to read from.
	 * @return a CNF; not null
	 * @throws IOException if the reader encounters a problem.
	 * @throws ParseException if the input does not conform to the DIMACS CNF file format
	 */
	@Nonnull
	public Node read(String in) throws ParseException, IOException {
		return read(new StringReader(in));
	}

	/**
	 * Reads the problem definition.
	 *
	 * @throws ParseException if the input does not conform to the DIMACS CNF file format
	 * @throws IOException
	 */
	private void readProblem(BufferedReader reader) throws ParseException, IOException {
		final String line = readToken(reader);
		if (line == null) {
			throw new ParseException("Invalid problem format", -1);
		}
		final String[] tokens = line.split("\\s+");
		if (tokens.length != 4) {
			throw new ParseException("Invalid problem format", -1);
		}
		if (!DIMACSFormat.PROBLEM.equals(tokens[0])) {
			throw new ParseException("Missing problem definition", -1);
		}
		if (!DIMACSFormat.CNF.equals(tokens[1])) {
			throw new ParseException("Problem type is not CNF", -1);
		}

		try {
			variableCount = Integer.parseInt(tokens[2]);
		} catch (final NumberFormatException e) {
			throw new ParseException("Variable count is not an integer", -1);
		}
		if (variableCount <= 0) {
			throw new ParseException("Variable count is not positive", -1);
		}

		try {
			clauseCount = Integer.parseInt(tokens[3]);
		} catch (final NumberFormatException e) {
			throw new ParseException("Clause count is not an integer", -1);
		}
		if (clauseCount <= 0) {
			throw new ParseException("Clause count is not positive", -1);
		}
	}

	/**
	 * Reads all clauses.
	 *
	 * @return all clauses; not null
	 * @throws ParseException if the input does not conform to the DIMACS CNF file format
	 * @throws IOException
	 */
	private Node[] readClauses(BufferedReader reader) throws ParseException, IOException {
		final Node[] clauses = new Node[clauseCount];
		for (int i = 0; i < clauseCount; i++) {
			final String[] tokens = readToken(reader).split("\\s+");
			if (tokens.length < 2) {
				throw new ParseException("Empty clause", -1);
			}
			final Node[] literals = new Node[tokens.length - 1];
			for (int j = 0; j < (tokens.length - 1); j++) {
				final String token = tokens[j];
				final int index;
				try {
					index = Integer.parseInt(token);
				} catch (final NumberFormatException e) {
					throw new ParseException("Illegal literal", -1);
				}
				if (index == 0) {
					throw new ParseException("Illegal literal", -1);
				}
				final Integer key = Math.abs(index);
				Object variable = indexVariables.get(key);
				if (variable == null) {
					variable = String.valueOf(key);
					indexVariables.put(key, variable);
				}
				literals[j] = new Literal(variable, index > 0);
			}
			if (!DIMACSFormat.CLAUSE_END.equals(tokens[tokens.length - 1])) {
				throw new ParseException("Illegal clause end", -1);
			}
			clauses[i] = new Or(literals);
		}
		return clauses;
	}

	/**
	 * Called when a comment is read.
	 *
	 * @param comment content of the comment; not null
	 * @return whether the comment was consumed logically
	 */
	private boolean readComment(String comment) {
		return readingVariables && readVariableDirectoryEntry(comment);
	}

	/**
	 * Reads an entry of the variable directory.
	 *
	 * @param line variable directory entry
	 * @return true if an entry was found
	 */
	private boolean readVariableDirectoryEntry(String line) {
		final String comment = line.substring(DIMACSFormat.COMMENT_START.length());
		final int firstSeparator = comment.indexOf(' ');
		if (firstSeparator <= 0) {
			return false;
		}
		final int index;
		try {
			index = Integer.parseInt(comment.substring(0, firstSeparator));
		} catch (final NumberFormatException e) {
			return false;
		}
		if (comment.length() < (firstSeparator + 2)) {
			return false;
		}
		final String variable = comment.substring(firstSeparator + 1);
		if (!indexVariables.containsKey(index)) {
			indexVariables.put(index, variable);
		}
		return true;
	}
}
