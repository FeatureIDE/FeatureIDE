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
package de.ovgu.featureide.fm.core.explanations.impl.ltms;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.explanations.FeatureModelExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.impl.AbstractFeatureModelExplanationCreator;

/**
 * Abstract implementation of {@link FeatureModelExplanationCreator} using an {@link Ltms LTMS}.
 * 
 * @author Timo Guenther
 * @author Sofia Ananieva
 */
public abstract class LtmsExplanationCreator extends AbstractFeatureModelExplanationCreator {
	/**
	 * The LTMS with the CNF as input.
	 * The LTMS is created lazily when needed and reset when the CNF changes.
	 */
	private Ltms ltms;
	
	/**
	 * Constructs a new instance of this class.
	 */
	public LtmsExplanationCreator() {
		super();
	}
	
	/**
	 * Constructs a new instance of this class.
	 * @param fm the feature model context
	 */
	public LtmsExplanationCreator(IFeatureModel fm) {
		super();
	}
	
	/**
	 * Returns the LTMS.
	 * Creates it first if necessary.
	 * @return the LTMS; not null
	 */
	protected Ltms getLTMS() {
		if (ltms == null) {
			setLTMS(createLTMS());
		}
		return ltms;
	}
	
	/**
	 * Sets the LTMS.
	 * @param ltms the LTMS
	 */
	protected void setLTMS(Ltms ltms) {
		this.ltms = ltms;
	}
	
	/**
	 * Returns a new LTMS with the CNF.
	 * @return a new LTMS with the CNF; not null
	 */
	protected Ltms createLTMS() {
		return new Ltms(getCNF());
	}
	
	@Override
	protected void setCNF(Node cnf) throws IllegalArgumentException {
		super.setCNF(cnf);
		setLTMS(null);
	}
}