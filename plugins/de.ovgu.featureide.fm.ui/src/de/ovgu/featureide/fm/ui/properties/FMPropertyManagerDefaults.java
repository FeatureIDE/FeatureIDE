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
package de.ovgu.featureide.fm.ui.properties;

import static de.ovgu.featureide.fm.core.localization.StringTable.ABSTRACT;

import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.QualifiedName;

import de.ovgu.featureide.fm.core.PluginID;

/**
 * Provides all {@link QualifiedName}s for the {@link FMPropertyManager}.
 *
 * @author Jens Meinicke
 */
public class FMPropertyManagerDefaults {

	static final QualifiedName QN_HIDE_LEGEND = createName("hidelegend");
	static final QualifiedName QN_LEGEND_FORGOUND = createName("legendforground");
	static final QualifiedName QN_LEGEND_BACKGROUND = createName("legendbackground");
	static final QualifiedName QN_LEGEND_BORDER = createName("legendboder");

	static final QualifiedName QN_LANGUAGE = createName("language");

	static final QualifiedName QN_DIAGRAM_BACKGROUND = createName("diagrambackground");
	static final QualifiedName QN_FEATURE_FORGROUND = createName("feature");
	static final QualifiedName QN_FEATURE_CONCRETE = createName("concrete");
	static final QualifiedName QN_FEATURE_ABSTRACT = createName(ABSTRACT);
	static final QualifiedName QN_FEATURE_HIDEEN_FORGROUND = createName("hiddenforground");
	static final QualifiedName QN_FEATURE_HIDEEN_BACKGROUND = createName("hiddenbackground");
	static final QualifiedName QN_FEATURE_DEAD = createName("dead");
	static final QualifiedName QN_FEATURE_FALSE_OPT = createName("falseoptional");
	static final QualifiedName QN_CONSTRAINT = createName("constraint");
	static final QualifiedName QN_CONNECTION = createName("connection");
	static final QualifiedName QN_WARNING = createName("warning");
	static final QualifiedName QN_HIDE_BORDER_COLOR = createName("hideBorderColor");
	static final QualifiedName QN_FEATURE_BORDER = createName("featureborder");
	static final QualifiedName QN_INHERITED_FEATURE_BORDER = createName("inheritedFeatureborder");
	static final QualifiedName QN_IMPORTED_FEATURE_BORDER = createName("inheritedFeatureborder");
	static final QualifiedName QN_INTERFACED_FEATURE_BORDER = createName("interfaceFeatureborder");

	static final QualifiedName QN_LAYOUT_MARGIN_X = createName("margin_x");
	static final QualifiedName QN_LAYOUT_MARGIN_Y = createName("margin_y");
	static final QualifiedName QN_FEATURE_X = createName("feature_x");
	static final QualifiedName QN_FEATURE_Y = createName("feature_y");
	static final QualifiedName QN_CONSTRAINT_SPACE = createName("constraint_space");

	static final String TRUE = "true";
	static final String FALSE = "false";

	public static final IWorkspaceRoot workspaceRoot = ResourcesPlugin.getWorkspace().getRoot();

	/**
	 * Creates a Qualified name.
	 *
	 * @param name the identifier for the QualifiedName
	 * @return The new QualifiedName
	 */
	static QualifiedName createName(String name) {
		return new QualifiedName(PluginID.PLUGIN_ID + "." + name, PluginID.PLUGIN_ID + "." + name);
	}
}
