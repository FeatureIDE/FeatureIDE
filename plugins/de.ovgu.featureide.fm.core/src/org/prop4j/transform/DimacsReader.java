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
import java.util.LinkedList;
import java.util.List;
import java.util.Scanner;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;

/**
 * Transforms DIMACS CNF files into instances of {@link Node}.
 * 
 * @author Timo Guenther
 */
public class DimacsReader {
	/** Token leading the problem definition. */
	private static final String PROBLEM = "p";
	/** Token identifying the problem type as CNF. */
	private static final String CNF = "cnf";
	
	/** The source to read from. */
	private final Readable in;
	/** The scanner for tokenizing the input. */
	private Scanner scanner;
	
	/** The amount of variables in the problem. */
	private int variableCount;
	/** The amount of clauses in the problem. */
	private int clauseCount;
	
	/**
	 * Constructs a new instance of this class with the given string.
	 * @param s input to read from; not null
	 */
	public DimacsReader(String s) {
		this(new StringReader(s));
	}
	
	/**
	 * Constructs a new instance of this class with the given input.
	 * @param in input to read from; not null
	 */
	public DimacsReader(Readable in) {
		this.in = in;
	}
	
	/**
	 * Reads the input.
	 * @return a CNF; not null
	 * @throws ParseException if the input does not conform to the DIMACS CNF file format
	 */
	public Node read() throws ParseException {
		try (final Scanner sc = new Scanner(in)) {
			this.scanner = sc;
			readProblem();
			return new And(readClauses().toArray(new Node[clauseCount]));
		}
	}
	
	/**
	 * Reads the problem definition.
	 * @throws ParseException if the input does not conform to the DIMACS CNF file format
	 */
	private void readProblem() throws ParseException {
		if (!scanner.hasNext() || !PROBLEM.equals(scanner.next())) {
			throw new ParseException("Missing problem definition", -1);
		}
		
		if (!scanner.hasNext() || !CNF.equals(scanner.next())) {
			throw new ParseException("Problem type is not CNF", -1);
		}
		
		if (!scanner.hasNextInt()) {
			throw new ParseException("Missing variable count", -1);
		}
		variableCount = scanner.nextInt();
		if (variableCount <= 0) {
			throw new ParseException("Variable count is not positive", -1);
		}
		
		if (!scanner.hasNextInt()) {
			throw new ParseException("Missing clause count", -1);
		}
		clauseCount = scanner.nextInt();
		if (clauseCount <= 0) {
			throw new ParseException("Clause count is not positive", -1);
		}
	}
	
	/**
	 * Reads all clauses.
	 * @return all clauses; not null
	 * @throws ParseException if the input does not conform to the DIMACS CNF file format
	 */
	private List<Node> readClauses() throws ParseException {
		final List<Node> clauses = new ArrayList<>(clauseCount);
		for (int i = 0; i < clauseCount; i++) {
			clauses.add(readClause());
		}
		return clauses;
	}
	
	/**
	 * Reads a single clause.
	 * @return a clause; not null
	 * @throws ParseException if the input does not conform to the DIMACS CNF file format
	 */
	private Node readClause() throws ParseException {
		List<Literal> literals = new LinkedList<>();
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
	 * @return a literal; null if there are no more literals in the clause
	 * @throws ParseException if the input does not conform to the DIMACS CNF file format
	 */
	private Literal readLiteral() throws ParseException {
		if (!scanner.hasNextInt()) {
			if (!scanner.hasNext()) {
				return null;
			}
			throw new ParseException("Illegal literal", -1);
		}
		final int index = scanner.nextInt();
		return createLiteral(index);
	}
	
	/**
	 * Creates a literal from the given index.
	 * @param index index of the literal
	 * @return a literal; null if the index is 0
	 */
	private Literal createLiteral(int index) {
		boolean positive = index > 0;
		if (index == 0) {
			return null;
		}
		return new Literal(String.valueOf(Math.abs(index)), positive);
	}
}