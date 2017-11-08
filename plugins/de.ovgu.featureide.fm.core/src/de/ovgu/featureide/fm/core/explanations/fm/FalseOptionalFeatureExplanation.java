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
package de.ovgu.featureide.fm.core.explanations.fm;

import org.prop4j.Implies;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * An explanation for a false-optional feature in a feature model.
 *
 * @author Timo G&uuml;nther
 */
public class FalseOptionalFeatureExplanation extends FeatureModelExplanation<IFeature> {

	/**
	 * Constructs a new instance of this class
	 *
	 * @param subject the subject to be explained
	 */
	public FalseOptionalFeatureExplanation(IFeature subject) {
		super(subject);
	}

	@Override
	public Node getImplication() {
		return new Implies(NodeCreator.getVariable(FeatureUtils.getParent(getSubject())), NodeCreator.getVariable(getSubject()));
	}

	@Override
	public FalseOptionalFeatureExplanationWriter getWriter() {
		return new FalseOptionalFeatureExplanationWriter(this);
	}
}
