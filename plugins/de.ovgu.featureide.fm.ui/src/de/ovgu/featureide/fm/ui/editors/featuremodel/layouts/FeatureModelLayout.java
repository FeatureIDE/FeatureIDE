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
package de.ovgu.featureide.fm.ui.editors.featuremodel.layouts;

import org.abego.treelayout.Configuration;
import org.eclipse.draw2d.geometry.Point;

/**
 * Encapsulates layout functionality for the feature model.
 *
 * @author soenke
 */
public class FeatureModelLayout implements IExtendedFeatureModelLayout {

	private boolean usesAbegoTreeLayout;
	private Configuration.Location abegoRootposition;

	private boolean autoLayoutLegend;
	private boolean showHiddenFeatures;
	private boolean showCollapsedConstraints;
	private boolean hasVerticalLayout;
	private Point legendPos;

	private int selectedLayoutAlgorithm;
	private boolean showShortNames;

	public FeatureModelLayout() {
		autoLayoutLegend = true;
		showHiddenFeatures = true;
		showCollapsedConstraints = false;
		hasVerticalLayout = true;
		legendPos = new Point(0, 0);
		selectedLayoutAlgorithm = 4;
		usesAbegoTreeLayout = false;
	}

	protected FeatureModelLayout(FeatureModelLayout featureModelLayout) {
		autoLayoutLegend = featureModelLayout.autoLayoutLegend;
		showHiddenFeatures = featureModelLayout.showHiddenFeatures;
		showCollapsedConstraints = featureModelLayout.showCollapsedConstraints;
		hasVerticalLayout = featureModelLayout.hasVerticalLayout;
		legendPos = featureModelLayout.legendPos.getCopy();
		selectedLayoutAlgorithm = featureModelLayout.selectedLayoutAlgorithm;
		usesAbegoTreeLayout = featureModelLayout.usesAbegoTreeLayout;
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
	public boolean showCollapsedConstraints() {
		return showCollapsedConstraints;
	}

	@Override
	public void showCollapsedConstraints(boolean b) {
		showCollapsedConstraints = b;
	}

	@Override
	public boolean verticalLayout() {
		return hasVerticalLayout;
	}

	@Override
	public void verticalLayout(boolean b) {
		hasVerticalLayout = b;
	}

//	// provisorisch: ! (unschön)
//	public void bottomUpLayout(boolean b) {
//		hasBottomUpLayout = b;
//	}
//
//	public boolean bottomUpLayout() {
//		return hasBottomUpLayout;
//	}
//
//	private boolean hasBottomUpLayout;
//	// -------------------------

	@Override
	public Point getLegendPos() {
		return legendPos;
	}

	@Override
	public void setLegendPos(int x, int y) {
		legendPos = new Point(x, y);
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

	/**
	 * @return the usesAbegoTreeLayout
	 */
	public boolean isUsesAbegoTreeLayout() {
		return usesAbegoTreeLayout;
	}

	/**
	 * @param usesAbegoTreeLayout the usesAbegoTreeLayout to set
	 */
	public void setUsesAbegoTreeLayout(boolean usesAbegoTreeLayout) {
		// a default root position:
		abegoRootposition = Configuration.Location.Bottom;
		this.usesAbegoTreeLayout = usesAbegoTreeLayout;
	}

	/**
	 * @return the abegoRootposition
	 */
	public Configuration.Location getAbegoRootposition() {
		return abegoRootposition;
	}

	/**
	 * @param abegoRootposition the abegoRootposition to set
	 */
	public void setAbegoRootposition(Configuration.Location abegoRootposition) {
		usesAbegoTreeLayout = true;
		this.abegoRootposition = abegoRootposition;
	}
}
