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
package org.prop4j.transform;

import static org.junit.Assert.assertTrue;

import org.junit.Test;
import org.prop4j.CNFDistributiveLawTransformer;
import org.prop4j.Node;

import de.ovgu.featureide.Commons;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * Tests for {@link CNFDistributiveLawTransformer}.
 *
 * @author Sebastian Krieter
 */
public class CNFDistributiveLawTransformerTest {

	@Test
	public void transformTimeout() {
		final IFeatureModel model = Commons.loadBenchmarkFeatureModelFromFile("berkeley_db_model.xml");
		final FeatureModelFormula featureModelFormula = new FeatureModelFormula(model);
		final Node propositionalNode = featureModelFormula.getPropositionalNode();
		assertTrue(propositionalNode.toCNF(true, true, 1).isEmpty());
		assertTrue(propositionalNode.toCNF(true, true, 1000).isPresent());
	}

}
