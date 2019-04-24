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
package de.ovgu.featureide.fm.core.io.propositionalModel;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;

/**
 * Transforms instances of {@link Node} into MODEL CNF file format.
 *
 * @author Timo G&uuml;nther
 */
public class ModelWriter {

	/** The clauses of the CNF to transform. */
	private List<Node> clauses;
	/** Maps variables to indexes. */
	private final Map<Object, Integer> variableIndexes = new LinkedHashMap<>();

	public String write(Node props) throws IllegalArgumentException {
		if (props == null) {
			throw new IllegalArgumentException("CNF is null");
		}

		try {
			clauses = props instanceof And ? Arrays.asList(props.getChildren()) : Collections.singletonList(props);

			final StringBuilder sb = new StringBuilder();
			final ArrayList<String> featureDirectory = new ArrayList<>();
			final ArrayList<String> Stringclauses = new ArrayList<>();
			final HashMap<String, ArrayList<String>> featureClauseMap = new HashMap<>();

			addVariables(props);
			constructFeatureDirectory(featureDirectory);
			constructClauses(Stringclauses);
			featureClauseMapping(featureDirectory, Stringclauses, featureClauseMap);
			writeModel(featureClauseMap, sb);

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
	 * Constructs the feature directory.
	 *
	 * @return the feature directory; not null
	 */
	private void constructFeatureDirectory(ArrayList<String> fd) {
		for (final Entry<Object, Integer> e : variableIndexes.entrySet()) {
			final String feature = e.getKey().toString();
			switch (feature.trim().toLowerCase()) {
			case "true":
			case "false":
				break;
			default:
				if (!feature.equals(MODELFormat.ROOT_IDENTIFIER)) {
					if (!feature.contains(MODELFormat.MODULE_FEATURE) && !feature.contains(MODELFormat.MODULES_FEATURE)) {
						fd.add(feature);
					}
				}
				break;
			}
		}
	}

	private void constructClauses(ArrayList<String> cd) {
		final Node parent = clauses.get(0);
		final Node[] childNodes = parent.getChildren();

		for (int i = 0; i < childNodes.length; i++) {
			final Node child = childNodes[i].toRegularCNF();
			String strClause = child.toString().replaceAll(" ", "");

			if (!strClause.contains(MODELFormat.ROOT_IDENTIFIER)) {
				for (final Literal l : child.getUniqueLiterals()) {
					final String searchFor = l.toString();
					final String replacement = "def(" + l.toString() + ")";
					final String replacementNeg = "!def(" + l.toString() + ")";

					if (l.positive) {
						strClause = strClause.replaceAll(searchFor, replacement);
					} else {
						strClause = strClause.replaceAll(searchFor, replacementNeg);
					}
				}
				strClause = strClause.replaceAll("-", "");
				cd.add(strClause);
			}
		}
	}

	/**
	 * Maps clauses to feature names
	 *
	 * @param fd feature directory = list of all feature names
	 * @param cd clause directory = list of all clauses
	 * @param fcm HashMap to the mapping
	 *
	 *        returns a Hashmap which contains clause to feature mapping
	 */
	private void featureClauseMapping(ArrayList<String> fd, ArrayList<String> cd, HashMap<String, ArrayList<String>> fcm) {
		final ArrayList<String> clauses = cd;
		final ArrayList<String> mappedClauses = new ArrayList<>();
		for (final String feature : fd) {
			mappedClauses.clear();
			final ArrayList<String> mapping = new ArrayList<>();
			for (final String clause : clauses) {
				if (clause.contains(feature)) {
					mappedClauses.add(clause);
					mapping.add(clause);
				}
			}
			fcm.put(feature, mapping);
			clauses.removeAll(mappedClauses);
		}
	}

	/**
	 * writes the clause to feature mapping
	 *
	 * @param fcm HashMap which contains the clause to feature mapping
	 * @param sb StringBuilder to create writable string
	 */
	private void writeModel(HashMap<String, ArrayList<String>> fcm, StringBuilder sb) {
		for (final String feature : fcm.keySet()) {
			sb.append(MODELFormat.FEATURE_START + " " + feature);
			sb.append(System.lineSeparator());
			for (final String clause : fcm.get(feature)) {
				sb.append(clause);
				sb.append(System.lineSeparator());
			}
		}
	}
}
