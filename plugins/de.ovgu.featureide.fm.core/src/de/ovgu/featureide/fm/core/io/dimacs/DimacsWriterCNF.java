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

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;

/**
 * Transforms instances of {@link Node} into DIMACS CNF file format.
 *
 * @author Timo Günther
 * @author Sebastian Krieter
 */
public class DimacsWriterCNF extends ADimacsWriter {

	private final CNF cnf;

	/**
	 * Constructs a new instance of this class with the given CNF.
	 *
	 * @param cnf the CNF to transform; not null
	 * @throws IllegalArgumentException if the input is null or not in CNF
	 */
	public DimacsWriterCNF(CNF cnf) throws IllegalArgumentException {
		super(Arrays.asList(cnf.getVariables().getNames()).subList(1, cnf.getVariables().size() + 1));
		this.cnf = cnf;
	}

	/**
	 * Writes the given clause.
	 *
	 * @param sb the string builder that builds the document
	 * @param clause clause to transform; not null
	 */
	private void writeClause(StringBuilder sb, LiteralSet clause) {
		for (final int l : clause.getLiterals()) {
			writeLiteral(sb, l);
			sb.append(" ");
		}
		sb.append(CLAUSE_END);
		sb.append(System.lineSeparator());
	}

	/**
	 * Writes the given literal.
	 *
	 * @param sb the string builder that builds the document
	 * @param l literal to transform; not null
	 */
	private void writeLiteral(StringBuilder sb, int l) {
		sb.append(String.valueOf(l));
	}

	@Override
	protected int getNumberOfClauses() {
		return cnf.getClauses().size();
	}

	@Override
	protected void writeClauses(StringBuilder sb) {
		for (final LiteralSet clause : cnf.getClauses()) {
			writeClause(sb, cnf.getInternalVariables().convertToInternal(clause).clean());
		}
	}

}
