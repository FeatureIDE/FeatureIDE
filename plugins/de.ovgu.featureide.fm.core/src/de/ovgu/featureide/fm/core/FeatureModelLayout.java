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
package de.ovgu.featureide.fm.core;

/**
 * TODO description
 * 
 * @author soenke
 */
public class FeatureModelLayout {
    private boolean autoLayoutLegend = true;
    private boolean showHiddenFeatures = true;
    private boolean hasVerticalLayout = true;
    private FMPoint legendPos = new FMPoint(0, 0);

    private int selectedLayoutAlgorithm = 1;

    public void setLegendAutoLayout(boolean b) {
	autoLayoutLegend = b;
    }

    public boolean hasLegendAutoLayout() {
	return autoLayoutLegend;
    }

    public boolean showHiddenFeatures() {
	return showHiddenFeatures;
    }

    public void showHiddenFeatures(boolean b) {
	showHiddenFeatures = b;
    }

    public boolean verticalLayout() {
	return hasVerticalLayout;
    }

    public void verticalLayout(boolean b) {
	hasVerticalLayout = b;
    }

    public FMPoint getLegendPos() {
	return legendPos;
    }

    public void setLegendPos(int x, int y) {
	this.legendPos = new FMPoint(x, y);
    }

    public void setLayout(int newLayoutAlgorithm) {
	selectedLayoutAlgorithm = newLayoutAlgorithm;
    }

    public int getLayoutAlgorithm() {
	return selectedLayoutAlgorithm;
    }

    public boolean hasFeaturesAutoLayout() {
	return (selectedLayoutAlgorithm != 0);
    }
}
