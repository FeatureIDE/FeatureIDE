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
package de.ovgu.featureide.fm.core.constraint.analysis;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.constraint.Equation;
import de.ovgu.featureide.fm.core.constraint.FeatureAttributeMap;
import de.ovgu.featureide.fm.core.constraint.Reference;
import de.ovgu.featureide.fm.core.constraint.RelationOperator;
import de.ovgu.featureide.fm.core.constraint.WeightedTerm;
import de.ovgu.featureide.fm.core.functional.Functional;

/**
 * The Translator utility provides a bunch of handy tools to translate feature models and their associated rules in the internal model to apply analysis.
 *
 * @author Sebastian Henneberg
 * @author Marcus Pinnecke (Feature Interface)
 */
public class Translator {

	/**
	 * Creates a bijective mapping between the first n natural numbers and the features present in the model.
	 *
	 * @param fm The feature model.
	 * @return 1-to-1 mapping of natural numbers to features.
	 */
	public static HashMap<String, Integer> buildFeatureNameMap(IFeatureModel fm, UniqueId idGen) {
		final HashMap<String, Integer> m = new HashMap<>();

		for (final CharSequence f : Functional.mapToString(fm.getFeatures())) {
			m.put(f.toString(), idGen.getNext());
		}

		return m;
	}

	/**
	 * Extends the given bijective mapping by all features present in the passed model which are not yet in the mapping.
	 *
	 * @param map 1-to-1 mapping of natural numbers to features.
	 * @param fm The feature model.
	 * @param idGen
	 */
	public static void extendFeatureNameMap(HashMap<String, Integer> m, IFeatureModel fm, UniqueId idGen) {

		for (final CharSequence f : Functional.mapToString(fm.getFeatures())) {
			if (!m.containsKey(f)) {
				m.put(f.toString(), idGen.getNext());
			}
		}
	}

	public static <T> void createAssumption(int id, boolean assumption, Collection<T> rs, RestrictionFactory<T> factory) {

		final List<Term> terms = new ArrayList<Term>();
		terms.add(new Term(id, 1, assumption));
		factory.createAndAdd(terms, RelationOperator.GREATER_EQUAL, 1, rs);
	}

	/**
	 * @param <T>
	 * @param map
	 * @param fm
	 * @param factory
	 * @return
	 */
	public static <T> List<T> translateFm(Map<String, Integer> map, IFeatureModel fm, RestrictionFactory<T> factory) {

		final List<T> rs = translateFmTree(map, fm, factory);
		rs.addAll(translateFmConstraints(map, fm, factory));

		return rs;
	}

	/**
	 * @category tree
	 */
	public static <T> List<T> translateFmTree(Map<String, Integer> map, IFeatureModel fm, RestrictionFactory<T> factory) {
		final List<T> rs = new ArrayList<T>();

		// root has to be included (r == 1)
		createAssumption(map.get(fm.getStructure().getRoot().getFeature().getName()), true, rs, factory);

		translateFmTree(map, fm.getStructure().getRoot(), rs, factory);

		return rs;
	}

	/**
	 * @category constraints
	 */
	public static <T> List<T> translateFmConstraints(Map<String, Integer> m, IFeatureModel fm, RestrictionFactory<T> factory) {
		final List<T> rs = new ArrayList<T>();

		translateFmConstraints(m, fm.getConstraints(), rs, factory);

		return rs;
	}

	/**
	 * @category tree
	 */
	private static <T> void translateFmTree(Map<String, Integer> m, IFeatureStructure feature, List<T> rs, RestrictionFactory<T> factory) {

		if (feature.isAlternative()) {
			translateFmTreeAlternative(m, feature, rs, factory);
		} else if (feature.isOr()) {
			translateFmTreeOr(m, feature, rs, factory);
		} else if (feature.isAnd()) {
			translateFmTreeAnd(m, feature, rs, factory);
		}

		for (final IFeatureStructure child : feature.getChildren()) {
			translateFmTree(m, child, rs, factory);
		}
	}

	/**
	 * @category tree helper
	 */
	private static <T> void translateFmTreeAlternative(Map<String, Integer> m, IFeatureStructure f, List<T> rs, RestrictionFactory<T> factory) {

		final List<Term> terms = new ArrayList<Term>();
		terms.add(new Term(m.get(f.getFeature().getName()), 1, true));

		for (final IFeatureStructure child : f.getChildren()) {
			terms.add(new Term(m.get(child.getFeature().getName()), -1, true));
		}

		// +p -c_1 -c_2 ... -c_n == 0
		factory.createAndAdd(terms, RelationOperator.EQUAL, 0, rs);
	}

	/**
	 * @category tree helper
	 */
	private static <T> void translateFmTreeOr(Map<String, Integer> m, IFeatureStructure f, List<T> rs, RestrictionFactory<T> factory) {

		final int numChildren = f.getChildren().size();

		final List<Term> terms = new ArrayList<Term>();
		terms.add(new Term(m.get(f.getFeature().getName()), numChildren, true));

		for (final IFeatureStructure child : f.getChildren()) {
			terms.add(new Term(m.get(child.getFeature().getName()), -1, true));
		}

		// -p +c_1 +c_2 ... +c_n >= 0
		factory.createAndAdd(terms, RelationOperator.GREATER_EQUAL, 0, rs);
		// -p +c_1 +c_2 ... +c_n <= (n-1)
		factory.createAndAdd(terms, RelationOperator.LESS_EQUAL, numChildren - 1, rs);

	}

	/**
	 * @category tree helper
	 */
	private static <T> void translateFmTreeAnd(Map<String, Integer> m, IFeatureStructure f, List<T> rs, RestrictionFactory<T> factory) {

		for (final IFeatureStructure child : f.getChildren()) {
			final List<Term> terms1 = new ArrayList<Term>();
			final List<Term> terms2 = new ArrayList<Term>();
			terms1.add(new Term(m.get(f.getFeature().getName()), 1, true));
			terms2.add(new Term(m.get(f.getFeature().getName()), 1, true));
			terms1.add(new Term(m.get(child.getFeature().getName()), -1, true));
			terms2.add(new Term(m.get(child.getFeature().getName()), -1, true));

			if (child.isMandatory()) {
				factory.createAndAdd(terms1, RelationOperator.EQUAL, 0, rs);
			} else {
				factory.createAndAdd(terms2, RelationOperator.GREATER_EQUAL, 0, rs);
			}
		}
	}

	/**
	 * @category constraints
	 */
	private static <T> void translateFmConstraints(Map<String, Integer> map, List<IConstraint> fmConstraints, List<T> rs, RestrictionFactory<T> factory) {

		for (final IConstraint fmConstraint : fmConstraints) {

			final Node cnfNode = fmConstraint.getNode().clone().toCNF();

			if (cnfNode instanceof Literal) {
				literal2Constraint(map, rs, (Literal) cnfNode, factory);
			} else if (cnfNode instanceof Or) {
				clause2Constraint(map, rs, (Or) cnfNode, factory);
			} else if (cnfNode instanceof And) {
				for (final Node clause : cnfNode.getChildren()) {
					if (clause instanceof Literal) {
						literal2Constraint(map, rs, (Literal) clause, factory);
					} else if (clause instanceof Or) {
						clause2Constraint(map, rs, (Or) clause, factory);
					}
					// clause2Constraint(map, rs, (Or) clause, factory);
				}
			}
		}
	}

	/**
	 * Translates a CNF literal into a pseudo boolean restriction.
	 *
	 * @category constraints helper
	 */
	private static <T> void literal2Constraint(Map<String, Integer> map, List<T> rs, Literal l, RestrictionFactory<T> factory) {

		final List<Term> terms = new ArrayList<Term>();
		terms.add(new Term(map.get(l.var), 1, l.positive));

		factory.createAndAdd(terms, RelationOperator.GREATER_EQUAL, 1, rs);
	}

	/**
	 * Translates a CNF clause into a pseudo boolean restriction
	 *
	 * @category constraints helper
	 */
	private static <T> void clause2Constraint(Map<String, Integer> map, List<T> rs, Or clause, RestrictionFactory<T> factory) {

		final List<Term> terms = new ArrayList<Term>();
		for (final Node node : clause.getChildren()) {
			final Literal l = (Literal) node;
			terms.add(new Term(map.get(l.var), 1, l.positive));
		}

		factory.createAndAdd(terms, RelationOperator.GREATER_EQUAL, 1, rs);
	}

	/**
	 * @category equations
	 */
	public static <T> List<T> translateEquations(Map<String, Integer> map, IFeatureModel fm, FeatureAttributeMap<Integer> attributes, List<Equation> equations,
			RestrictionFactory<T> factory) {

		final List<T> rs = new ArrayList<T>();

		for (final Equation equation : equations) {

			// process the variables
			final List<Term> terms = new ArrayList<Term>();
			for (final WeightedTerm term : equation.getWeightedTerms()) {
				transformVars(map, fm, attributes, terms, term);
			}

			// adding the equation to the constrains
			factory.createAndAdd(terms, equation.getOperator(), equation.getDegree(), rs);
		}

		return rs;
	}

	/**
	 * @category equations helper
	 */
	private static void transformVars(Map<String, Integer> map, IFeatureModel fm, FeatureAttributeMap<Integer> attributes, List<Term> terms,
			WeightedTerm term) {

		int coefficient = term.getWeight();
		final Reference ref = term.getReference();

		switch (ref.getType()) {
		case FEATURE:
			terms.add(new Term(map.get(ref.getFeatureName()), coefficient, term.isPositive()));
			break;

		case ATTRIBUTE:
			coefficient *= attributes.getAttribute(ref.getFeatureName(), ref.getAttributeName()).getValue();
			terms.add(new Term(map.get(ref.getFeatureName()), coefficient, term.isPositive()));
			break;

		case ATTRIBUTE_SUM:
			for (final String feature : getSubtreeFeatureNames(fm, ref.getFeatureName())) {
				final Integer attribute = attributes.getAttribute(feature, ref.getAttributeName()).getValue();
				if (attribute != null) {
					final int newCoefficient = coefficient * attribute;
					terms.add(new Term(map.get(feature), newCoefficient, term.isPositive()));
				}
			}
			break;
		}
	}

	/**
	 * @category equations helper
	 */
	private static List<String> getSubtreeFeatureNames(IFeatureModel fm, String featureName) {

		final List<String> result = new ArrayList<String>();

		final Queue<IFeatureStructure> bfsStack = new LinkedList<>();
		bfsStack.add(fm.getFeature(featureName).getStructure());
		while (!bfsStack.isEmpty()) {
			final IFeatureStructure feature = bfsStack.poll();
			result.add(feature.getFeature().getName());
			for (final IFeatureStructure childFeature : feature.getChildren()) {
				bfsStack.add(childFeature);
			}
		}

		return result;
	}
}
