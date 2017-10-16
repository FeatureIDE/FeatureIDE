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
package de.ovgu.featureide.core.signature.filter;

import java.util.Arrays;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.base.AFeatureData;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.filter.base.IFilter;

public class ContextFilter implements IFilter<AbstractSignature> {

	private final ProjectSignatures projectSignatures;
	private final Node fmNode;
	private final boolean[] selectedFeatures;
	private SatSolver solver;

	public ContextFilter(String featureName, ProjectSignatures projectSignatures) {
		this(new Node[] { new Literal(featureName, true) }, projectSignatures);
	}

	public ContextFilter(Node[] constraints, ProjectSignatures projectSignatures) {
		this.projectSignatures = projectSignatures;
		fmNode = AdvancedNodeCreator.createNodes(projectSignatures.getFeatureModel());
		selectedFeatures = new boolean[projectSignatures.getFeatureModel().getNumberOfFeatures()];

		init(constraints);
	}

	public void init(String featureName) {
		init(new Node[] { new Literal(featureName, true) });
	}

	public void init(Node[] constraints) {
		final Node[] fixClauses = new Node[constraints.length + 1];
		fixClauses[0] = fmNode;
		System.arraycopy(constraints, 0, fixClauses, 1, constraints.length);
		Arrays.fill(selectedFeatures, false);

		solver = new SatSolver(new And(fixClauses), 2000);

		for (final Literal literal : solver.knownValues(SatSolver.ValueType.TRUE)) {
			final int id = projectSignatures.getFeatureID(literal.var.toString());
			if (id > -1) {
				selectedFeatures[id] = true;
			}
		}
	}

	@Override
	public boolean isValid(AbstractSignature signature) {
		final AFeatureData[] ids = signature.getFeatureData();
		final Node[] negativeLiterals = new Node[ids.length];
		for (int i = 0; i < ids.length; ++i) {
			final int id = ids[i].getID();
			if (selectedFeatures[id]) {
				return true;
			}
			negativeLiterals[i] = new Literal(projectSignatures.getFeatureName(id), false);
		}
		try {
			return !solver.isSatisfiable(negativeLiterals);
		} catch (final TimeoutException e) {
			CorePlugin.getDefault().logError(e);
			return false;
		}
	}

}
