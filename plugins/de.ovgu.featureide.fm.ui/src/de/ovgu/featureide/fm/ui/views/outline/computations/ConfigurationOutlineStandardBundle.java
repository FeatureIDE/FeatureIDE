/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.views.outline.computations;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.views.outline.IOutlineEntry;
import de.ovgu.featureide.fm.ui.views.outline.computations.impl.ManuallySelectedFeatureCountComputation;
import de.ovgu.featureide.fm.ui.views.outline.computations.impl.ManuallyUnselectedFeatureCountComputation;
import de.ovgu.featureide.fm.ui.views.outline.computations.impl.SelectedFeatureCountComputation;
import de.ovgu.featureide.fm.ui.views.outline.computations.impl.UndecidedFeatureCountComputation;
import de.ovgu.featureide.fm.ui.views.outline.computations.impl.UnselectedFeatureCountComputation;

/**
 * Standard properties of the configuration Additional properties/computataions regarding the config can be attached as child
 *
 * @author Chico Sundermann
 */
public class ConfigurationOutlineStandardBundle implements IOutlineEntry {

	private static final String LABEL = "Configuration statistics";

	private Configuration config;

	public ConfigurationOutlineStandardBundle(Configuration config) {
		this.config = config;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.IOutlineEntry#getLabel()
	 */
	@Override
	public String getLabel() {
		return LABEL;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.IOutlineEntry#getLabelImage()
	 */
	@Override
	public Image getLabelImage() {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.IOutlineEntry#hasChildren()
	 */
	@Override
	public boolean hasChildren() {
		return true;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.IOutlineEntry#getChildren()
	 */
	@Override
	public List<IOutlineEntry> getChildren() {
		final List<IOutlineEntry> entries = new ArrayList<>();
		entries.add(new SelectedFeatureCountComputation(config));
		entries.add(new ManuallySelectedFeatureCountComputation(config));
		entries.add(new UnselectedFeatureCountComputation(config));
		entries.add(new ManuallyUnselectedFeatureCountComputation(config));
		entries.add(new UndecidedFeatureCountComputation(config));
		return entries;
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

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.IOutlineEntry#handleDoubleClick()
	 */
	@Override
	public void handleDoubleClick() {
		// TODO Auto-generated method stub
		FMUIPlugin.getDefault().logInfo("DOUBLE CLICKED");
	}

}
