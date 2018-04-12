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
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.annotation.Nonnull;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;

/**
 * Transforms DIMACS CNF files into instances of {@link Node}.
 *
 * @author Timo G&uuml;nther
 * @author Sebastian Krieter
 */
public class DimacsReader {

	private static final Pattern commentPattern = Pattern.compile("\\A" + DIMACSFormat.COMMENT + "\\s*(.*)\\Z");
	private static final Pattern problemPattern = Pattern.compile("\\A\\s*" + DIMACSFormat.PROBLEM + "\\s+" + DIMACSFormat.CNF + "\\s+(\\d+)\\s+(\\d+)");

	/** Maps indexes to variables. */
	private final Map<Integer, Object> indexVariables = new LinkedHashMap<>();
	/**
	 * The amount of variables as declared in the problem definition. May differ from the actual amount of variables found.
	 */
	private int variableCount;
	/** The amount of clauses in the problem. */
	private int clauseCount;
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
			final LineIterator lineIterator = new LineIterator(reader);
			lineIterator.nextLine();

			readComments(lineIterator);
			readProblem(lineIterator);
			readComments(lineIterator);
			readingVariables = false;

			final Node[] clauses = readClauses(lineIterator);
			final int actualVariableCount = indexVariables.size();
			if (variableCount != actualVariableCount) {
				throw new ParseException(String.format("Found %d instead of %d variables", actualVariableCount, variableCount), 1);
			}
			return new And(clauses);
		} finally {
			indexVariables.clear();
			variableCount = -1;
			clauseCount = -1;
		}
	}

	private void readComments(final LineIterator lineIterator) {
		for (String line = lineIterator.currentLine(); line != null; line = lineIterator.nextLine()) {
			final Matcher matcher = commentPattern.matcher(line);
			if (matcher.matches()) {
				readComment(matcher.group(1)); // read comments ...
			} else {
				break; // ... until a non-comment token is found.
			}
		}
	}

	private static class LineIterator {
		private final BufferedReader reader;
		private String line = null;
		private int lineCount = 0;

		public LineIterator(BufferedReader reader) {
			this.reader = reader;
		}

		public String nextLine() {
			try {
				do {
					line = reader.readLine();
					if (line == null) {
						return null;
					}
					lineCount++;
				} while (line.trim().isEmpty());
				return line;
			} catch (final IOException e) {
				return null;
			}
		}

		public String currentLine() {
			return line;
		}

		public void setCurrentLine(String line) {
			this.line = line;
		}

		public int getLineCount() {
			return lineCount;
		}

	};

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
			lineIterator.nextLine();
		} else {
			lineIterator.setCurrentLine(trail);
		}

		try {
			variableCount = Integer.parseInt(matcher.group(1));
		} catch (final NumberFormatException e) {
			throw new ParseException("Variable count is not an integer", lineIterator.getLineCount());
		}
		if (variableCount <= 0) {
			throw new ParseException("Variable count is not positive", lineIterator.getLineCount());
		}

		try {
			clauseCount = Integer.parseInt(matcher.group(2));
		} catch (final NumberFormatException e) {
			throw new ParseException("Clause count is not an integer", lineIterator.getLineCount());
		}
		if (clauseCount <= 0) {
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
	private Node[] readClauses(LineIterator lineIterator) throws ParseException, IOException {
		final LinkedList<String> literalQueue = new LinkedList<>();
		final Node[] clauses = new Node[clauseCount];
		int readClausesCount = 0;
		for (String line = lineIterator.currentLine(); line != null; line = lineIterator.nextLine()) {
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

				clauses[readClausesCount] = parseClause(readClausesCount, clauseSize, literalQueue, lineIterator);
				readClausesCount++;

				if (!DIMACSFormat.CLAUSE_END.equals(literalQueue.removeFirst())) {
					throw new ParseException("Illegal clause end", lineIterator.getLineCount());
				}
				literalList = literalQueue;
			} while (!literalQueue.isEmpty());
		}
		if (!literalQueue.isEmpty()) {
			clauses[readClausesCount] = parseClause(readClausesCount, literalQueue.size(), literalQueue, lineIterator);
			readClausesCount++;
		}
		if (readClausesCount < clauseCount) {
			throw new ParseException(String.format("Found %d instead of %d clauses", readClausesCount, clauseCount), 1);
		}
		return clauses;
	}

	private Or parseClause(int readClausesCount, int clauseSize, LinkedList<String> literalQueue, LineIterator lineIterator) throws ParseException {
		if (readClausesCount == clauseCount) {
			throw new ParseException(String.format("Found more than %d clauses", clauseCount), 1);
		}
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
			Object variable = indexVariables.get(key);
			if (variable == null) {
				variable = String.valueOf(key);
				indexVariables.put(key, variable);
			}
			literals[j] = new Literal(variable, index > 0);
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
		if (!indexVariables.containsKey(index)) {
			indexVariables.put(index, variable);
		}
		return true;
	}
}
