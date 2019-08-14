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
package de.ovgu.featureide.fm.core.io.propositionalModel;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.text.ParseException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;

import javax.annotation.Nonnull;

import org.prop4j.And;
import org.prop4j.Node;
import org.prop4j.NodeReader;

/**
 * Transforms MODEL propositional logic files into instances of {@link Node}.
 *
 * @author Timo G&uuml;nther
 * @author Sebastian Krieter
 */
public class ModelReader {

	private ArrayList<String> featureDirectory;
	private And clausesDirectory;

	/**
	 * Reads the input.
	 *
	 * @param in The source to read from.
	 * @throws IOException if the reader encounters a problem.
	 * @throws ParseException if the input does not conform to the MODEL CNF file format
	 */
	@Nonnull
	public void read(Reader in) throws ParseException, IOException {
		final HashSet<String> features = new HashSet<>();
		final ArrayList<String> clausesString = new ArrayList<>();

		try (final BufferedReader reader = new BufferedReader(in)) {
			final LineIterator lineIterator = new LineIterator(reader);

			while (lineIterator.nextLine() != null) {
				final String line = lineIterator.currentLine().trim();
				if (!line.startsWith("#item") && !line.contains("#choice")) {
					final String[] splitString = line.replaceAll("\\(|!|def|\\||&|\\)", " ").split("\\s+");
					if (splitString != null) {
						for (final String feature : splitString) {
							if (!feature.isEmpty()) {
								features.add(feature);
							}
						}
					}
					clausesString.add(line.replaceAll("\\s+|def", ""));
				}
			}

			featureDirectory = new ArrayList<>(features);
			clausesDirectory = new And(readClauses(clausesString, features));
		}

	}

	public ArrayList<String> getFeatures(String in) throws ParseException, IOException {
		if (featureDirectory == null) {
			read(in);
		}
		return featureDirectory;

	}

	public Node getClauses(String in) throws ParseException, IOException {
		if (clausesDirectory == null) {
			read(in);
		}
		return clausesDirectory;
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
	 * @throws IOException if the reader encounters a problem.
	 * @throws ParseException if the input does not conform to the MODEL CNF file format
	 */
	@Nonnull
	public void read(String in) throws ParseException, IOException {
		read(new StringReader(in));
	}

	/**
	 * Reads all clauses.
	 *
	 * @return all clauses; not null
	 * @throws ParseException if the input does not conform to the MODEL CNF file format
	 * @throws IOException
	 */
	private Node[] readClauses(ArrayList<String> stringClauses, Collection<String> featureNames) throws ParseException, IOException {
		final NodeReader reader = new NodeReader();
		reader.setFeatureNames(featureNames);
		reader.activatePropositionalModelSymbols();

		final List<Node> clauses = new ArrayList<>(stringClauses.size());
		for (final String stringClause : stringClauses) {
			final Node clause = reader.stringToNode(stringClause.replaceAll("(\\||&|!)", " $1 "));
			if (clause != null) {
				clauses.add(clause);
			}
		}
		return clauses.toArray(new Node[0]);
	}

}
