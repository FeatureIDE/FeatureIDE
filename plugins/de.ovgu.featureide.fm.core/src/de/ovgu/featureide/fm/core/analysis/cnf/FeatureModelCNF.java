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
package de.ovgu.featureide.fm.core.analysis.cnf;

import java.util.ArrayList;
import java.util.List;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * Represents an instance of a satisfiability problem in CNF.
 *
 * @author Sebastian Krieter
 */
public class FeatureModelCNF extends CNF {

	private static final long serialVersionUID = -4656146001706586124L;

	protected final IFeatureModel featureModel;

	protected final List<ClauseOrigin> origins = new ArrayList<>();

	protected final boolean useOldNames;

	public FeatureModelCNF(IFeatureModel featureModel) {
		this(featureModel, false);
	}

	public FeatureModelCNF(IFeatureModel featureModel, boolean useOldNames) {
		super(new Variables(useOldNames ? FeatureUtils.getOldFeatureNamesList(featureModel) : FeatureUtils.getFeatureNamesList(featureModel)));
		this.featureModel = featureModel;
		this.useOldNames = useOldNames;
	}

	public FeatureModelCNF(FeatureModelCNF oldSatInstance, boolean copyClauses) {
		super(oldSatInstance, copyClauses);
		featureModel = oldSatInstance.featureModel;
		useOldNames = oldSatInstance.useOldNames;
	}

	public FeatureModelCNF(FeatureModelCNF oldSatInstance) {
		this(oldSatInstance, true);
	}

}
