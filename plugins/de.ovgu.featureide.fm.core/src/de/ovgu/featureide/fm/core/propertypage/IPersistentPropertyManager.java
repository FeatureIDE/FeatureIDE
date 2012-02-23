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
package de.ovgu.featureide.fm.core.propertypage;

import org.eclipse.draw2d.Border;
import org.eclipse.swt.graphics.Color;

import de.ovgu.featureide.fm.core.propertypage.ILanguage;

/**
 * Manages all persistent properties defined at the property pages.<br>
 * These settings are defined for the whole workspace.
 * 
 * @author Jens Meinicke
 */
public interface IPersistentPropertyManager {

	public void setHideLegend(boolean value);

	public boolean isLegendHidden();

	public void setLegendForgroundColor(Color color);

	public Color getLegendForgroundColor();

	public void setLegendBackgroundColor(Color color);

	public Color getLegendBackgroundColor();

	public void setLegendBorderColor(Color color);

	public Color getLegendBorderColor();

	public Color getFeatureForgroundColor();

	public void setFeatureForgroundColor(Color color);

	public Color getDiagramBackgroundColor();

	public void setDiagramBackgroundColor(Color color);

	public Color getConcreteFeatureBackgroundColor();

	public void setConcreteFeatureBackgroundColor(Color color);

	public Color getAbstractFeatureBackgroundColor();

	public void setAbstractFeatureBackgroundColor(Color color);

	public Color getHiddenFeatureForgroundColor();

	public void setHiddenFeatureForgroundColor(Color color);

	public Color getHiddenFeatureBackgroundColor();

	public void setHiddenFeatureBackgroundColor(Color color);

	public Color getDeadFeatureBackgroundColor();

	public void setDeadFeatureBackgroundColor(Color color);

	public Color getConstraintBackgroundColor();

	public void setConstraintBackgroundColor(Color color);

	public Color getConnectionForgroundColor();

	public void setConnectionForgroundColor(Color color);

	public Color getWarningColor();

	public void setWarningColor(Color color);

	public void setLanguage(String text);

	public ILanguage getLanguage();

	public int getLayoutMarginX();

	public void setlayoutMagrginX(int value);

	public int getLayoutMarginY();

	public void setlayoutMagrginY(int value);

	public int getFeatureSpaceX();

	public void setFeatureSpaceX(int value);

	public int getFeatureSpaceY();

	public void setFeatureSpaceY(int value);

	public int getConstraintSpace();

	public void setConstraintSpace(int value);

	public Color getConstrinatBorderColor(boolean selected);

	public Border getConstrinatBorder(boolean selected);

	public Border getHiddenFeatureBorder(boolean selected);

	public Border getDeadFeatureBorder(boolean selected);

	public Border getLegendBorder();

	public Border getConcreteFeatureBorder(boolean selected);

	public Border getAbsteactFeatureBorder(boolean selected);

	public Border getHiddenLegendBorder();

	public Color getDecoratorForgroundColor();

	public Color getDecoratorBackgroundColor();
	
}