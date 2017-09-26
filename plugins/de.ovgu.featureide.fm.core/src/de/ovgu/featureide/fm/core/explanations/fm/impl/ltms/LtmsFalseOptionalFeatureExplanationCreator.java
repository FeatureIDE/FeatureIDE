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
package de.ovgu.featureide.fm.core.explanations.fm.impl.ltms;

import java.util.Collection;
import java.util.Set;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.explanations.fm.FalseOptionalFeatureExplanation;
import de.ovgu.featureide.fm.core.explanations.fm.FalseOptionalFeatureExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.impl.ltms.Ltms;

/**
 * Implementation of {@link FalseOptionalFeatureExplanationCreator} using an {@link Ltms LTMS}.
 *
 * @author Sofia Ananieva
 * @author Timo G&uuml;nther
 */
public class LtmsFalseOptionalFeatureExplanationCreator extends LtmsFeatureModelExplanationCreator implements FalseOptionalFeatureExplanationCreator {

	@Override
	public IFeature getSubject() {
		return (IFeature) super.getSubject();
	}

	@Override
	public void setSubject(Object subject) throws IllegalArgumentException {
		if ((subject != null) && !(subject instanceof IFeature)) {
			throw new IllegalArgumentException("Illegal subject type");
		}
		super.setSubject(subject);
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p> Sets initial truth value assumptions of the false-optional feature to false and its parent to true. Then propagates the values until a violation in a
	 * clause occurs. </p>
	 */
	@Override
	public FalseOptionalFeatureExplanation getExplanation() throws IllegalStateException {
		final Ltms ltms = getOracle();
		ltms.clearPremises();
		ltms.addPremise(NodeCreator.getVariable(getSubject()), false);
		ltms.addPremise(NodeCreator.getVariable(FeatureUtils.getParent(getSubject())), true);
		return getExplanation(ltms.getExplanations());
	}

	@Override
	protected FalseOptionalFeatureExplanation getExplanation(Collection<Set<Integer>> clauseIndexes) {
		return (FalseOptionalFeatureExplanation) super.getExplanation(clauseIndexes);
	}

	@Override
	protected FalseOptionalFeatureExplanation getConcreteExplanation() {
		return new FalseOptionalFeatureExplanation(getSubject());
	}
}
