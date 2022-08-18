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
package de.ovgu.featureide.fm.core.io.dimacs;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.text.ParseException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;

/**
 * Transforms DIMACS CNF files into instances of {@link Node}.
 *
 * @author Timo Günther
 * @author Sebastian Krieter
 */
public class DimacsReader {

	private static final Pattern commentPattern = Pattern.compile("\\A" + DIMACSConstants.COMMENT + "\\s*(.*)\\Z");
	private static final Pattern problemPattern = Pattern.compile("\\A\\s*" + DIMACSConstants.PROBLEM + "\\s+" + DIMACSConstants.CNF + "\\s+(\\d+)\\s+(\\d+)");

	/** Maps indexes to variables. */
	private final List<String> indexVariables = new ArrayList<>();
	/**
	 * The amount of variables as declared in the problem definition. May differ from the actual amount of variables found.
	 */
	private int variableCount;
	/** The amount of clauses in the problem. */
	private int clauseCount;
	/** True to read the variable directory for naming variables. */
	private boolean readVariableDirectory = false;
	private boolean flattenCNF = false;
	/** True when currently reading the comment section at the beginning of the file and parsing variable names. */
	private boolean readingVariables;

	/**
	 * <p> Sets the reading variable directory flag. If true, the reader will look for a variable directory in the comments. This contains names for the
	 * variables which would otherwise just be numbers. </p>
	 *
	 * <p> Defaults to false. </p>
	 *
	 * @param readVariableDirectory whether to read the variable directory
	 */
	public void setReadingVariableDirectory(boolean readVariableDirectory) {
		this.readVariableDirectory = readVariableDirectory;
	}

	/**
	 * <p> Sets the flatten CNF flag. If true, the reader will try to compact the resulting CNF nodes by replacing node with just one child with their
	 * child.</p>
	 *
	 * <p> Defaults to false. </p>
	 *
	 * @param flattenCNF whether to flatten the resulting CNF node
	 */
	public void setFlattenCNF(boolean flattenCNF) {
		this.flattenCNF = flattenCNF;
	}

	/**
	 * Reads the input.
	 *
	 * @param in The source to read from.
	 * @return a CNF; not null
	 * @throws IOException if the reader encounters a problem.
	 * @throws ParseException if the input does not conform to the DIMACS CNF file format
	 */
	public Node read(Reader in) throws ParseException, IOException {
		indexVariables.clear();
		indexVariables.add(null);
		variableCount = -1;
		clauseCount = -1;
		readingVariables = readVariableDirectory;
		try (final BufferedReader reader = new BufferedReader(in)) {
			final LineIterator lineIterator = new LineIterator(reader);
			lineIterator.get();

			readComments(lineIterator);
			readProblem(lineIterator);
			readComments(lineIterator);
			readingVariables = false;

			for (int i = 1; i < indexVariables.size(); i++) {
				if (indexVariables.get(i) == null) {
					indexVariables.set(i, Integer.toString(i));
				}
			}
			while (indexVariables.size() <= variableCount) {
				indexVariables.add(Integer.toString(indexVariables.size()));
			}

			final ArrayList<Node> clauses = readClauses(lineIterator);
			final int actualVariableCount = indexVariables.size() - 1;
			if (variableCount != actualVariableCount) {
				throw new ParseException(String.format("Found %d instead of %d variables", actualVariableCount, variableCount), 1);
			}
			final int actualClausesCount = clauses.size();
			if (clauseCount != actualClausesCount) {
				throw new ParseException(String.format("Found %d instead of %d clauses", actualClausesCount, clauseCount), 1);
			}
			Node node = new And(clauses);
			if (flattenCNF) {
				node = node.simplifyTree();
			}
			return node;
		}
	}

	private void readComments(final LineIterator lineIterator) {
		for (String line = lineIterator.currentLine(); line != null; line = lineIterator.get()) {
			final Matcher matcher = commentPattern.matcher(line);
			if (matcher.matches()) {
				readComment(matcher.group(1)); // read comments ...
			} else {
				break; // ... until a non-comment token is found.
			}
		}
	}

	/**
	 * Reads the input. Calls {@link #read(Reader)}.
	 *
	 * @param in The string to read from.
	 * @return a CNF; not null
	 * @throws IOException if the reader encounters a problem.
	 * @throws ParseException if the input does not conform to the DIMACS CNF file format
	 */
	public Node read(String in) throws ParseException, IOException {
		return read(new StringReader(in));
	}

	/**
	 * Reads the problem definition.
	 *
	 * @throws ParseException if the input does not conform to the DIMACS CNF file format
	 */
	private void readProblem(LineIterator lineIterator) throws ParseException {
		final String line = lineIterator.currentLine();
		if (line == null) {
			throw new ParseException("Invalid problem format", lineIterator.getLineCount());
		}
		final Matcher matcher = problemPattern.matcher(line);
		if (!matcher.find()) {
			throw new ParseException("Invalid problem format", lineIterator.getLineCount());
		}
		final String trail = line.substring(matcher.end());
		if (trail.trim().isEmpty()) {
			lineIterator.get();
		} else {
			lineIterator.setCurrentLine(trail);
		}

		try {
			variableCount = Integer.parseInt(matcher.group(1));
		} catch (final NumberFormatException e) {
			throw new ParseException("Variable count is not an integer", lineIterator.getLineCount());
		}
		if (variableCount < 0) {
			throw new ParseException("Variable count is not positive", lineIterator.getLineCount());
		}

		try {
			clauseCount = Integer.parseInt(matcher.group(2));
		} catch (final NumberFormatException e) {
			throw new ParseException("Clause count is not an integer", lineIterator.getLineCount());
		}
		if (clauseCount < 0) {
			throw new ParseException("Clause count is not positive", lineIterator.getLineCount());
		}
	}

	/**
	 * Reads all clauses.
	 *
	 * @return all clauses; not null
	 * @throws ParseException if the input does not conform to the DIMACS CNF file format
	 * @throws IOException
	 */
	private ArrayList<Node> readClauses(LineIterator lineIterator) throws ParseException, IOException {
		final LinkedList<String> literalQueue = new LinkedList<>();
		final ArrayList<Node> clauses = new ArrayList<>(clauseCount);
		for (String line = lineIterator.currentLine(); line != null; line = lineIterator.get()) {
			if (commentPattern.matcher(line).matches()) {
				continue;
			}
			List<String> literalList = Arrays.asList(line.trim().split("\\s+"));
			literalQueue.addAll(literalList);

			do {
				final int clauseEndIndex = literalList.indexOf("0");
				if (clauseEndIndex < 0) {
					break;
				}
				final int clauseSize = literalQueue.size() - (literalList.size() - clauseEndIndex);
				if (clauseSize <= 0) {
					throw new ParseException("Empty clause", lineIterator.getLineCount());
				}

				clauses.add(parseClause(clauseSize, literalQueue, lineIterator));

				if (!DIMACSConstants.CLAUSE_END.equals(literalQueue.removeFirst())) {
					throw new ParseException("Illegal clause end", lineIterator.getLineCount());
				}
				literalList = literalQueue;
			} while (!literalQueue.isEmpty());
		}
		if (!literalQueue.isEmpty()) {
			clauses.add(parseClause(literalQueue.size(), literalQueue, lineIterator));
		}
		return clauses;
	}

	private Or parseClause(int clauseSize, LinkedList<String> literalQueue, LineIterator lineIterator) throws ParseException {
		final Node[] literals = new Node[clauseSize];
		for (int j = 0; j < literals.length; j++) {
			final String token = literalQueue.removeFirst();
			final int index;
			try {
				index = Integer.parseInt(token);
			} catch (final NumberFormatException e) {
				throw new ParseException("Illegal literal", lineIterator.getLineCount());
			}
			if (index == 0) {
				throw new ParseException("Illegal literal", lineIterator.getLineCount());
			}
			final Integer key = Math.abs(index);
			if (indexVariables.size() <= key) {
				throw new ParseException("Variable count is smaller than given literal", lineIterator.getLineCount());
			}
			literals[j] = new Literal(indexVariables.get(key), index > 0);
		}
		return new Or(literals);
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
	private boolean readVariableDirectoryEntry(String comment) {
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
		while (indexVariables.size() <= index) {
			indexVariables.add(null);
		}
		if (indexVariables.get(index) == null) {
			indexVariables.set(index, variable);
		}
		return true;
	}

	public List<String> getVariables() {
		return indexVariables.subList(1, indexVariables.size());
	}

}
