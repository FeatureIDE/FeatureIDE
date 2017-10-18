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
package de.ovgu.featureide.fm.core.conversion;

import java.util.LinkedList;
import java.util.List;

import org.prop4j.And;
import org.prop4j.Node;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * @brief Converter using cnf and nnf.
 *
 * @author Alexander Knueppel
 */
public class CombinedConverter implements IConverterStrategy {

	private final List<IConverterStrategy> strategies = new LinkedList<IConverterStrategy>();
	private final IConverterStrategy bestStrategy = new NNFConverter();

	private final double w_f = 1.0; // weight for features
	private final double w_c = 1.0; // weight for simple constraints

	/**
	 *
	 * @param node
	 * @return
	 */
	private double estimatedCosts(Node node) {
		double costs = w_f;

		if (!(node instanceof And) && !(node instanceof Or)) {
			return w_f + w_c;
		}

		for (final Node child : node.getChildren()) {
			costs += estimatedCosts(child);
		}
		return costs;
	}

	/**
	 *
	 * @param preprocessed
	 * @return
	 */
	private double estimatedCosts(List<Node> preprocessed) {
		double costs = w_f; // costs for top-feature
		for (final Node node : preprocessed) {
			// recognize simple constraints
			if (ComplexConstraintConverter.isSimple(node)) {
				costs += w_c;
				continue;
			}
			costs += estimatedCosts(node);
		}
		// System.out.println(costs);
		return costs;
	}

	public CombinedConverter() {
		strategies.add(new NNFConverter());
		strategies.add(new CNFConverter());
	}

	@Override
	public List<Node> preprocess(IConstraint constraint) {
		List<Node> result = new LinkedList<Node>();

		double costs = Double.MAX_VALUE;
		for (final IConverterStrategy strat : strategies) {
			final List<Node> preprocessed = strat.preprocess(constraint);
			double cost = 0;
			if ((cost = estimatedCosts(preprocessed)) < costs) {
				result = preprocessed;
				costs = cost;
			}
		}
		return result;
	}

	@Override
	public IFeatureModel convert(IFeatureModel fm, List<Node> nodes, boolean preserve) {
		// CNF and NNF have the same creation process...
		// This here might be fixed in the future to work for other strategies as well.
		return bestStrategy.convert(fm, nodes, preserve);
	}
}
