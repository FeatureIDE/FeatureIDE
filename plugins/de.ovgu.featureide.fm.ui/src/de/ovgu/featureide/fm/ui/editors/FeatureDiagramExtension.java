/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.editors;

import java.util.LinkedList;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.Platform;
import org.eclipse.draw2d.Figure;
import org.eclipse.jface.action.IMenuManager;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConnectionEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.FeatureFigure;

/**
 * Extension point of the FeatureDiagram.
 * @see de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor
 * @author Jens Meinicke
 */
public class FeatureDiagramExtension {

	/**
	 * Extends the context menu.
	 * @param menu the context menu
	 * @param featureDiagramEditor the feature diagram editor
	 * @see de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor
	 */
	public void extendContextMenu(IMenuManager menu, FeatureDiagramEditor featureDiagramEditor){
		
	}
	
	/**
	 * Extends the tool tip of the feature figure.
	 * @param toolTipContent the original tool tip
	 * @param figure the feature figure
	 * @return the revised tool tip
	 * @see de.ovgu.featureide.fm.ui.editors.featuremodel.figures.FeatureFigure
	 */
	public Figure extendFeatureFigureToolTip(Figure toolTipContent, FeatureFigure figure) {
		return toolTipContent;
	}

	/**
	 * Extends the tool tip of the connection part.
	 * @param toolTipContent the original tool tip
	 * @param connectionEditPart the connection edit part
	 * @return the revised tool tip
	 * @see de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConnectionEditPart
	 */
	public Figure extendConnectionToolTip(Figure toolTipContent, ConnectionEditPart connectionEditPart) {
		return toolTipContent;
	}
	
	/**
	 * @return all extensions of the feature diagram 
	 * @see de.ovgu.featureide.fm.ui.FeatureDiagram
	 */
	public static LinkedList<FeatureDiagramExtension> getExtensions() {
		LinkedList<FeatureDiagramExtension> extensions = new LinkedList<FeatureDiagramExtension>();

		IConfigurationElement[] config = Platform.getExtensionRegistry()
				.getConfigurationElementsFor(
						FMUIPlugin.PLUGIN_ID + ".FeatureDiagram");
		try {
			for (IConfigurationElement e : config) {
				final Object o = e.createExecutableExtension("class");
				if (o instanceof FeatureDiagramExtension) {
					extensions.add(((FeatureDiagramExtension) o));
				}
			}
		} catch (Exception e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return extensions;
	}

}
