/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import org.prop4j.And;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 *  @brief Converter using conjunctive normal form.
 * 
 * @author Alexander Knueppel
 */
public class BestConverter implements IConverterStrategy {
	
	List<IConverterStrategy> strategies = new LinkedList<IConverterStrategy>(); 
	IConverterStrategy bestStrategy = null;
	private int estimatedCosts(List<Node> preprocessed) {
		return 0;
	}
	
	public BestConverter() {
		strategies.add(new NNFConverter());
		strategies.add(new CNFConverter());
	}
	@Override
	public List<Node> preprocess(IConstraint constraint) {
		List<Node> result = new LinkedList<Node>();
	
		int costs = Integer.MAX_VALUE;
		for(IConverterStrategy strat : strategies) {
			List<Node> preprocessed = strat.preprocess(constraint);
			int cost = 0;
			if((cost = estimatedCosts(preprocessed)) < costs) {
				result = preprocessed;
				costs = cost;
				bestStrategy = strat;
			}
		}		
		return result;
	}
	
	@Override
	public IFeatureModel convert(IFeatureModel fm, List<Node> nodes, boolean preserve) {
		return bestStrategy.convert(fm, nodes, preserve);
	}
}
