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

import java.util.HashMap;
import java.util.LinkedList;

import javax.annotation.Nonnull;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.color.FeatureColor;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;

/**
 * Represents a feature at the {@link FSTModel}.<br> Contains {@link FSTRole}s with their corresponding {@link FSTClass}.
 *
 * @author Jens Meinicke
 * @author Marcus Pinnecke (Feature Interface)
 */
public class FSTFeature {

	private final HashMap<String, FSTRole> roles = new HashMap<String, FSTRole>();
	protected String name;
	private final FSTModel model;
	private static final int hashCodePrime = 37;
	private boolean hasMethodContracts = false;

	public FSTFeature(String name, final FSTModel model) {
		this.name = name;
		this.model = model;
	}

	public boolean isSelected() {
		final FSTConfiguration config = model.getConfiguration();
		if (config != null) {
			return config.getSelectedFeatures().contains(name);
		}
		return false;
	}

	public int getColor() {
		if (model == null) {
			return FeatureColor.NO_COLOR.getValue();
		}
		final IFeatureModel featureModel = model.getFeatureProject().getFeatureModel();
		final IFeature feature = featureModel.getFeature(name);
		return FeatureColorManager.getColor(feature).getValue();
	}

	public String getName() {
		return name;
	}

	@Nonnull
	public LinkedList<FSTRole> getRoles() {
		return new LinkedList<FSTRole>(roles.values());
	}

	public FSTRole getRole(String className) {
		return roles.get(className);
	}

	public boolean hasMethodContracts() {
		return hasMethodContracts;
	}

	public void setMethodContracts(boolean hasMethodContracts) {
		this.hasMethodContracts = hasMethodContracts;
	}

	@Override
	public String toString() {
		return name;
	}

	/**
	 * @param className
	 * @param role
	 */
	public void addRole(String className, FSTRole role) {
		roles.put(className, role);
	}

	@Override
	public boolean equals(Object feature) {
		if (feature == this) {
			return true;
		}
		if (!(feature instanceof FSTFeature)) {
			return false;
		}
		final FSTFeature comp = (FSTFeature) feature;
		if (!comp.getName().equals(getName()) || !comp.model.getFeatureProject().getProjectName().equals(model.getFeatureProject().getProjectName())) {
			return false;
		}
		return true;
	}

	@Override
	public int hashCode() {
		if (model != null) {
			int hashCode = 1;
			hashCode = (hashCodePrime * hashCode) + getName().hashCode();
			return (hashCodePrime * hashCode) + model.getFeatureProject().getProjectName().hashCode();
		} else {
			return super.hashCode();
		}
	}
}
