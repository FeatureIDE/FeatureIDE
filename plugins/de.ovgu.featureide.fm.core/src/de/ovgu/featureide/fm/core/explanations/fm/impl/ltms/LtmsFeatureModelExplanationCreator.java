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
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.fm.impl.AbstractFeatureModelExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.impl.ltms.Ltms;

/**
 * Abstract implementation of {@link FeatureModelExplanationCreator} using an {@link Ltms LTMS}.
 *
 * @author Timo G&uuml;nther
 * @author Sofia Ananieva
 */
public abstract class LtmsFeatureModelExplanationCreator extends AbstractFeatureModelExplanationCreator {

	/**
	 * The LTMS with the CNF as input. The LTMS is created lazily when needed and reset when the CNF changes.
	 */
	private Ltms ltms;

	/**
	 * Constructs a new instance of this class.
	 */
	protected LtmsFeatureModelExplanationCreator() {
		super();
	}

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param fm the feature model context
	 */
	protected LtmsFeatureModelExplanationCreator(IFeatureModel fm) {
		super();
	}

	/**
	 * Returns the LTMS. Creates it first if necessary.
	 *
	 * @return the LTMS; not null
	 */
	protected Ltms getLtms() {
		if (ltms == null) {
			setLtms(createLtms());
		}
		return ltms;
	}

	/**
	 * Sets the LTMS.
	 *
	 * @param ltms the LTMS
	 */
	protected void setLtms(Ltms ltms) {
		this.ltms = ltms;
	}

	/**
	 * Returns a new LTMS with the CNF.
	 *
	 * @return a new LTMS with the CNF; not null
	 */
	protected Ltms createLtms() {
		return new Ltms(getCnf());
	}

	@Override
	protected Node setCnf() {
		final Node cnf = super.setCnf();
		if (cnf != null) {
			setLtms(null);
		}
		return cnf;
	}

	/**
	 * Returns the shortest explanation among the given ones. Note that this may not be the shortest one possible.
	 *
	 * @param clauseIndexes indexes of clauses of explanations to roll into one
	 * @return the shortest explanation among the given ones
	 */
	protected Explanation getExplanation(Collection<Set<Integer>> clauseIndexes) {
		final List<Explanation> explanations = new LinkedList<>();
		for (final Set<Integer> c : clauseIndexes) {
			explanations.add(getExplanation(c));
		}
		final Explanation cumulatedExplanation = getConcreteExplanation();
		cumulatedExplanation.setExplanationCount(0);
		Explanation shortestExplanation = null;
		for (final Explanation explanation : explanations) {
			cumulatedExplanation.addExplanation(explanation); // Remember that this explanation was generated.
			if ((shortestExplanation == null) || (explanation.getReasonCount() < shortestExplanation.getReasonCount())) {
				shortestExplanation = explanation; // Remember the shortest explanation.
			}
		}
		if (shortestExplanation == null) {
			return null;
		}
		shortestExplanation.setCounts(cumulatedExplanation); // Remember the reason and explanations that were generated before.
		return shortestExplanation;
	}
}
