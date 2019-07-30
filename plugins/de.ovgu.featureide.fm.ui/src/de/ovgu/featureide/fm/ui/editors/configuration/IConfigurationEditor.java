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
package de.ovgu.featureide.fm.ui.editors.configuration;

import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;

public interface IConfigurationEditor {

	ConfigurationManager getConfigurationManager();

	FeatureModelManager getFeatureModelManager();

	boolean isAutoSelectFeatures();

	void setAutoSelectFeatures(boolean autoSelectFeatures);

	boolean hasValidFeatureModel();

	boolean isIOError();

	boolean isReadConfigurationError();

	boolean isReadFeatureModelError();

	enum EXPAND_ALGORITHM {
		DEFUALT, OPEN_CLAUSE, PARENT, CHILDREN, PARENT_CLAUSE
	}

	EXPAND_ALGORITHM getExpandAlgorithm();

	void setExpandAlgorithm(EXPAND_ALGORITHM expandAlgorithm);

}
