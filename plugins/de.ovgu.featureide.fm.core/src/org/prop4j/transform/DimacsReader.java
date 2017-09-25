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

import java.io.StringReader;
import java.text.ParseException;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Scanner;

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

	/** Token leading a (single-line) comment. */
	private static final String COMMENT = "c";
	/** Token leading the problem definition. */
	private static final String PROBLEM = "p";
	/** Token identifying the problem type as CNF. */
	private static final String CNF = "cnf";

	/** The source to read from. */
	private final Readable in;
	/** The scanner for tokenizing the input. */
	private Scanner scanner;

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
	private boolean lastClause = false;
	/** True to read the variable directory for naming variables. */
	private boolean readingVariableDirectory = false;

	/**
	 * Constructs a new instance of this class with the given string.
	 *
	 * @param s input to read from; not null
	 */
	public DimacsReader(String s) {
		this(new StringReader(s));
	}

	/**
	 * Constructs a new instance of this class with the given input.
	 *
	 * @param in input to read from; not null
	 */
	public DimacsReader(Readable in) {
		this.in = in;
	}

	/**
	 * <p> Sets the reading variable directory flag. If true, the reader will look for a variable directory in the comments. This contains names for the
	 * variables which would otherwise just be numbers. </p>
	 *
	 * <p> Defaults to false. </p>
	 *
	 * @param readingVariableDirectory whether to read the variable directory
	 */
	public void setReadingVariableDirectory(boolean readingVariableDirectory) {
		this.readingVariableDirectory = readingVariableDirectory;
	}

	/**
	 * Reads the next non-comment token. Also reads any comments before it.
	 *
	 * @return the next token; null if already completely read and empty
	 * @throws ParseException if there is no token left in the input but the reader is not yet done
	 */
	private String readToken() throws ParseException {
		String token;
		while (true) {
			if (!scanner.hasNext()) {
				if (lastClause) {
					return null;
				}
				throw new ParseException("Unexpected end of input", -1);
			}
			token = scanner.next();
			if (COMMENT.equals(token)) {
				readComment(scanner.nextLine());
				continue; // Keep reading tokens...
			}
			break; // ... until a non-comment token is found.
		}
		return token;
	}

	/**
	 * Reads the input.
	 *
	 * @return a CNF; not null
	 * @throws IllegalStateException if this method has already been called on this instance before (reading multiple times is disallowed since {@link Readable}
	 *         cannot be reversed)
	 * @throws ParseException if the input does not conform to the DIMACS CNF file format
	 */
	public synchronized Node read() throws IllegalStateException, ParseException {
		if (scanner != null) {
			throw new IllegalStateException("Already read");
		}
		try (final Scanner scanner = new Scanner(in)) {
			this.scanner = scanner;
			readProblem();
			final List<Node> clauses = readClauses();
			if (readToken() != null) {
				throw new ParseException("Trailing data", -1);
			}
			final int actualVariableCount = indexVariables.size();
			if (variableCount != actualVariableCount) {
				throw new ParseException(String.format("Found %d instead of %d variables", actualVariableCount, variableCount), -1);
			}
			return new And(clauses.toArray(new Node[clauseCount]));
		}
	}

	/**
	 * Reads the problem definition.
	 *
	 * @throws ParseException if the input does not conform to the DIMACS CNF file format
	 */
	private void readProblem() throws ParseException {
		if (!PROBLEM.equals(readToken())) {
			throw new ParseException("Missing problem definition", -1);
		}

		if (!CNF.equals(readToken())) {
			throw new ParseException("Problem type is not CNF", -1);
		}

		try {
			variableCount = Integer.parseInt(readToken());
		} catch (final NumberFormatException e) {
			throw new ParseException("Variable count is not an integer", -1);
		}
		if (variableCount <= 0) {
			throw new ParseException("Variable count is not positive", -1);
		}

		try {
			clauseCount = Integer.parseInt(readToken());
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
	 */
	private List<Node> readClauses() throws ParseException {
		final List<Node> clauses = new ArrayList<>(clauseCount);
		for (int i = 0; !lastClause; i++) {
			if ((i + 1) == clauseCount) {
				lastClause = true;
			}
			clauses.add(readClause());
		}
		return clauses;
	}

	/**
	 * Reads a single clause.
	 *
	 * @return a clause; not null
	 * @throws ParseException if the input does not conform to the DIMACS CNF file format
	 */
	private Node readClause() throws ParseException {
		final List<Literal> literals = new LinkedList<>();
		Literal l = readLiteral();
		while (l != null) {
			literals.add(l);
			l = readLiteral();
		}
		if (literals.isEmpty()) {
			throw new ParseException("Empty clause", -1);
		}
		return new Or(literals.toArray(new Node[literals.size()]));
	}

	/**
	 * Reads a literal.
	 *
	 * @return a literal; null if there are no more literals in the clause
	 * @throws ParseException if the input does not conform to the DIMACS CNF file format
	 */
	private Literal readLiteral() throws ParseException {
		final String token = readToken();
		if (token == null) {
			return null;
		}
		final int index;
		try {
			index = Integer.parseInt(token);
		} catch (final NumberFormatException e) {
			throw new ParseException("Illegal literal", -1);
		}
		return createLiteral(index);
	}

	/**
	 * Creates a literal from the given index.
	 *
	 * @param index index of the literal
	 * @return a literal; null if the index is 0
	 */
	private Literal createLiteral(int index) {
		if (index == 0) {
			return null;
		}
		final Integer key = Math.abs(index);
		Object variable = indexVariables.get(key);
		if (variable == null) {
			variable = String.valueOf(key);
			indexVariables.put(key, variable);
		}
		return new Literal(variable, index > 0);
	}

	/**
	 * Called when a comment is read.
	 *
	 * @param comment content of the comment; not null
	 * @return whether the comment was consumed logically
	 */
	private boolean readComment(String comment) {
		if (readingVariableDirectory && readVariableDirectoryEntry(comment)) {
			return true;
		}
		return false;
	}

	/**
	 * Reads an entry of the variable directory.
	 *
	 * @param entry variable directory entry
	 * @return true if an entry was found
	 */
	private boolean readVariableDirectoryEntry(String entry) {
		try (final Scanner sc = new Scanner(entry)) {
			if (!sc.hasNextInt()) {
				return false;
			}
			final int index = sc.nextInt();
			if (!sc.hasNextLine()) {
				return false;
			}
			String variable = sc.nextLine();
			if ((variable.length() >= 2) && Character.isWhitespace(variable.codePointAt(0))) {
				variable = variable.substring(1); // remove a single separating whitespace character (but allow variables with whitespace after that)
			} else {
				return false;
			}
			if (!indexVariables.containsKey(index)) {
				indexVariables.put(index, variable);
			}
			return true;
		}
	}
}
