/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.properties;

import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.QualifiedName;

import de.ovgu.featureide.fm.core.FMCorePlugin;

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
	static final QualifiedName QN_FEATURE_ABSTRACT = createName("abstract");
	static final QualifiedName QN_FEATURE_HIDEEN_FORGROUND = createName("hiddenforground");
	static final QualifiedName QN_FEATURE_HIDEEN_BACKGROUND = createName("hiddenbackground");
	static final QualifiedName QN_FEATURE_DEAD = createName("dead");
	static final QualifiedName QN_FEATURE_FALSE_OPT = createName("falseoptional");
	static final QualifiedName QN_CONSTRAINT = createName("constraint");
	static final QualifiedName QN_CONNECTION = createName("connection");
	static final QualifiedName QN_WARNING = createName("warning");

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
	 * @param name the identifier for the QualifiedName
	 * @return The new QualifiedName
	 */
	static QualifiedName createName(String name) {
		return new QualifiedName(FMCorePlugin.PLUGIN_ID + "." + name, FMCorePlugin.PLUGIN_ID + "." + name);
	}
}
