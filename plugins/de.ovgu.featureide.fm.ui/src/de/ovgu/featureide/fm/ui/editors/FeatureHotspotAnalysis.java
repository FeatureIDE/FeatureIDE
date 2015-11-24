/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.editors;

import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURE_ORDER;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURE_HOTSPOT_ANALYSIS;

import org.eclipse.core.runtime.QualifiedName;

import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Display the hotspot analysis for the feature model.
 * 
 * @author Christopher Kruczek
 * @author Andy Kenner
 */
public class FeatureHotspotAnalysis extends FeatureModelEditorPage {

	private static final String ID = FMUIPlugin.PLUGIN_ID + ".editors.FeatureHotSpotAnalysis";
	private static final String PAGE_TEXT = FEATURE_HOTSPOT_ANALYSIS;
	
	@Override
	public String getID() {
		return ID;
	}

	
	@Override
	public String getPageText() {
		return PAGE_TEXT;
	}

}
