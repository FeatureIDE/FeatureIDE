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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.configuration;

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.localization.StringTable;

/**
 * Simple configuration format.</br> Lists all selected features in the user-defined order (if specified).
 *
 * @author Sebastian Krieter
 *
 * @see DefaultFormat
 */
public class ExpressionFormat extends DefaultFormat {

	public static final String ID = PluginID.PLUGIN_ID + ".format.config." + ExpressionFormat.class.getSimpleName();

	@Override
	public String getSuffix() {
		return StringTable.EXPRESSION;
	}

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public String getName() {
		return "Expression";
	}

}
