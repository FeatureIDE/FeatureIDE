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
package de.ovgu.featureide.fm.ui.views.outline.computations.impl;

import java.util.List;

import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.ui.views.outline.IOutlineEntry;

/**
 * This class computes the number of manually selected features in a given configuration
 *
 * @author Chico Sundermann
 */
public class ManuallySelectedFeatureCountComputation implements IOutlineEntry {

	private Configuration config;
	private static final String LABEL = "Number of manually selected features: ";

	public ManuallySelectedFeatureCountComputation(Configuration config) {
		this.config = config;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.IOutlineEntry#getLabel()
	 */
	@Override
	public String getLabel() {
		return LABEL + Integer.toString(calculateCount());
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.IOutlineEntry#getLabelImage()
	 */
	@Override
	public Image getLabelImage() {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.IOutlineEntry#hasChildren()
	 */
	@Override
	public boolean hasChildren() {
		// TODO Auto-generated method stub
		return false;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.IOutlineEntry#getChildren()
	 */
	@Override
	public List<IOutlineEntry> getChildren() {
		return null;
	}

	private int calculateCount() {
		int count = 0;
		for (final SelectableFeature feat : config.getFeatures()) {
			if ((feat.getManual() == Selection.SELECTED) && (feat.getAutomatic() == Selection.UNDEFINED)) {
				count++;
			}
		}
		return count;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.IOutlineEntry#supportsType(java.lang.Object)
	 */
	@Override
	public boolean supportsType(Object element) {
		return true;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.IOutlineEntry#setConfig(de.ovgu.featureide.fm.core.configuration.Configuration)
	 */
	@Override
	public void setConfig(Configuration config) {
		this.config = config;

	}

}
