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
package de.ovgu.featureide.fm.core.analysis.cnf.formula;

import java.util.HashMap;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.IVariables;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * Holds certain {@link ACreator elements} that can be derived from a feature model.
 *
 * @author Sebastian Krieter
 *
 * @see #getElement(ACreator)
 */
public class FeatureModelFormula {

	private final HashMap<ACreator<?>, ACreator<?>> map = new HashMap<>();

	/**
	 * Get an arbitrary element that can be derived from the associated feature model.<br/> This methods first checks whether there is a cached instance and
	 * only computes the requested object otherwise.
	 *
	 * @return a {@link Node} instance.
	 */
	@SuppressWarnings("unchecked")
	public <T> T getElement(ACreator<T> formulaElement) {
		ACreator<?> mappedFormulaElement;
		synchronized (map) {
			mappedFormulaElement = map.get(formulaElement);
			if (mappedFormulaElement == null) {
				map.put(formulaElement, formulaElement);
				formulaElement.init(this);
				mappedFormulaElement = formulaElement;
			}
		}
		return (T) mappedFormulaElement.get();
	}

	private final IFeatureModel featureModel;

	public FeatureModelFormula(IFeatureModel featureModel) {
		this.featureModel = featureModel;
	}

	public IFeatureModel getFeatureModel() {
		return featureModel;
	}

	public IVariables getVariables() {
		return getElement(new EmptyCNFCreator()).getVariables();
	}

	/**
	 * Get the CNF for the associated feature model.<br/> Convenience method, fully equivalent to {@code getElement(new CNFFormula())}.
	 *
	 * @return a {@link CNF} instance.
	 */
	public CNF getCNF() {
		return getElement(new CNFCreator());
	}

	/**
	 * Get the Node in CNF for the associated feature model.<br/> Convenience method, fully equivalent to {@code getElement(new CNFNode())}.
	 *
	 * @return a {@link Node} instance.
	 */
	public Node getCNFNode() {
		return getElement(new CNFNodeCreator());
	}

	public void resetFormula() {
		synchronized (map) {
			map.clear();
		}
	}

}
