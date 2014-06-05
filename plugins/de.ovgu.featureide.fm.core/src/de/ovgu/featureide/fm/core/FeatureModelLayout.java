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
package de.ovgu.featureide.fm.core;

/**
 * Encapsulates layout functionality for the feature model.
 * 
 * @author soenke
 */
public class FeatureModelLayout {
	private boolean autoLayoutLegend;
	private boolean showHiddenFeatures;
	private boolean hasVerticalLayout;
	private FMPoint legendPos;

	private int selectedLayoutAlgorithm;
	
	public FeatureModelLayout() {
		this.autoLayoutLegend = true;
		this.showHiddenFeatures = true;
		this.hasVerticalLayout = true;
		this.legendPos = new FMPoint(0, 0);
		this.selectedLayoutAlgorithm = 1;
	}
	
	protected FeatureModelLayout(FeatureModelLayout featureModelLayout) {
		this.autoLayoutLegend = featureModelLayout.autoLayoutLegend;
		this.showHiddenFeatures = featureModelLayout.showHiddenFeatures;
		this.hasVerticalLayout = featureModelLayout.hasVerticalLayout;
		this.legendPos = new FMPoint(featureModelLayout.legendPos.getX(), featureModelLayout.legendPos.getY());
		this.selectedLayoutAlgorithm = featureModelLayout.selectedLayoutAlgorithm;
	}

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
	
	public FeatureModelLayout clone() {
		return new FeatureModelLayout(this);
	}
}
