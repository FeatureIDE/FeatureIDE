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
package de.ovgu.featureide.core.fstmodel;

import java.util.Collection;
import java.util.Collections;

import org.eclipse.core.resources.IFile;

/**
 * Describes the configuration for the FSTModel, to determine whether a feature is selected.
 *
 * @author Jens Meinicke
 */
public class FSTConfiguration extends FSTFeature {

	private final IFile file;
	private final boolean selected;
	private Collection<String> selectedFeatures = Collections.emptySet();

	/**
	 *
	 * @param name The name of the configuration
	 * @param file The configuration file
	 * @param selected <code>true</code> if the configuration is the current configuration
	 */
	public FSTConfiguration(final String name, final IFile file, final boolean selected) {
		super(name, null);
		this.file = file;
		this.selected = selected;
	}

	public IFile getFile() {
		return file;
	}

	@Override
	public boolean isSelected() {
		return selected;
	}

	public void setSelectedFeatures(final Collection<String> selectedFeatures) {
		this.selectedFeatures = Collections.unmodifiableCollection(selectedFeatures);
	}

	/**
	 * @return the selectedFeatures
	 */
	public Collection<String> getSelectedFeatures() {
		return selectedFeatures;
	}

}
