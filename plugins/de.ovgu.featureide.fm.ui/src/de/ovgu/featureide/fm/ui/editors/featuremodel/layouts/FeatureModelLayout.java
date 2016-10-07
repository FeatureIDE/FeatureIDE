/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.editors.featuremodel.layouts;

import org.eclipse.draw2d.geometry.Point;

/**
 * Encapsulates layout functionality for the feature model.
 * 
 * @author soenke
 */
public class FeatureModelLayout implements IExtendedFeatureModelLayout {
	private boolean autoLayoutLegend;
	private boolean showHiddenFeatures;
	private boolean hasVerticalLayout;
	private Point legendPos;

	private int selectedLayoutAlgorithm;
	private boolean showShortNames;
	
	public FeatureModelLayout() {
		this.autoLayoutLegend = true;
		this.showHiddenFeatures = true;
		this.hasVerticalLayout = true;
		this.legendPos = new Point(0, 0);
		this.selectedLayoutAlgorithm = 1;
	}
	
	protected FeatureModelLayout(FeatureModelLayout featureModelLayout) {
		this.autoLayoutLegend = featureModelLayout.autoLayoutLegend;
		this.showHiddenFeatures = featureModelLayout.showHiddenFeatures;
		this.hasVerticalLayout = featureModelLayout.hasVerticalLayout;
		this.legendPos = featureModelLayout.legendPos.getCopy();
		this.selectedLayoutAlgorithm = featureModelLayout.selectedLayoutAlgorithm;
	}

	@Override
	public void setLegendAutoLayout(boolean b) {
		autoLayoutLegend = b;
	}

	@Override
	public boolean hasLegendAutoLayout() {
		return autoLayoutLegend;
	}
	
	@Override
	public boolean showShortNames() {
		return showShortNames;
	}

	@Override
	public void setShowShortNames(boolean b) {
		showShortNames = b;
	}

	@Override
	public boolean showHiddenFeatures() {
		return showHiddenFeatures;
	}

	@Override
	public void showHiddenFeatures(boolean b) {
		showHiddenFeatures = b;
	}

	@Override
	public boolean verticalLayout() {
		return hasVerticalLayout;
	}

	@Override
	public void verticalLayout(boolean b) {
		hasVerticalLayout = b;
	}

	@Override
	public Point getLegendPos() {
		return legendPos;
	}

	@Override
	public void setLegendPos(int x, int y) {
		this.legendPos = new Point(x, y);
	}

	@Override
	public void setLayout(int newLayoutAlgorithm) {
		selectedLayoutAlgorithm = newLayoutAlgorithm;
	}

	@Override
	public int getLayoutAlgorithm() {
		return selectedLayoutAlgorithm;
	}

	@Override
	public boolean hasFeaturesAutoLayout() {
		return (selectedLayoutAlgorithm != 0);
	}
	
	@Override
	public FeatureModelLayout clone() {
		return new FeatureModelLayout(this);
	}
}
