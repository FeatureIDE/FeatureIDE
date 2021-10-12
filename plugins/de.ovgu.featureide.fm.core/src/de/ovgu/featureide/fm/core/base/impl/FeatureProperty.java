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
package de.ovgu.featureide.fm.core.base.impl;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureProperty;

/**
 * All additional properties of an {@link IFeature}.
 *
 * @author Sebastian Krieter
 * @author Marcus Pinnecke
 */
public class FeatureProperty implements IFeatureProperty {

	protected final IFeature correspondingFeature;

	protected String description;
	protected boolean implicit;

	public FeatureProperty(FeatureProperty oldProperty, IFeature correspondingFeature) {
		this.correspondingFeature = correspondingFeature != null ? correspondingFeature : oldProperty.correspondingFeature;
		description = oldProperty.description.toString();
		implicit = oldProperty.implicit;
	}

	public FeatureProperty(IFeature correspondingFeature) {
		this.correspondingFeature = correspondingFeature;
		description = "";
		implicit = false;
	}

	@Override
	public IFeatureProperty clone(IFeature newFeature) {
		return new FeatureProperty(this, newFeature);
	}

	/**
	 *
	 * @return The description of the Feature.
	 */
	@Override
	public String getDescription() {
		return description;
	}

	@Override
	public String getDisplayName() {
		return correspondingFeature.getName();
	}

	@Override
	public IFeature getFeature() {
		return correspondingFeature;
	}

	@Override
	public void setDescription(final CharSequence description) {
		this.description = description.toString();
	}

	@Override
	public void setDisplayName(CharSequence name) {}

	@Override
	public boolean isConstraintSelected() {
		throw new UnsupportedOperationException("Not implemented yet");
	}

	@Override
	public boolean selectConstraint(boolean state) {
		throw new UnsupportedOperationException("Not implemented yet");
	}

	@Override
	public boolean isImplicit() {
		return implicit;
	}

	@Override
	public void setImplicit(boolean implicit) {
		this.implicit = implicit;
	}
}
