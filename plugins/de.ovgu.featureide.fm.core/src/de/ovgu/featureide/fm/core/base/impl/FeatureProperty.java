/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

import java.beans.PropertyChangeEvent;

import javax.annotation.CheckForNull;

import de.ovgu.featureide.fm.core.FeatureStatus;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureProperty;

/**
 * All additional properties of an {@link IFeature}.
 * 
 * @author Sebastian Krieter
 * 
 */
public class FeatureProperty implements IFeatureProperty, PropertyConstants {

	protected final IFeature correspondingFeature;

	protected CharSequence description;
	protected FeatureStatus status;

	public FeatureProperty(FeatureProperty oldProperty, IFeature correspondingFeature) {
		this.correspondingFeature = correspondingFeature != null ? correspondingFeature : oldProperty.correspondingFeature;

		description = new String(oldProperty.description.toString());
		status = oldProperty.status;
	}

	public FeatureProperty(IFeature correspondingFeature) {
		this.correspondingFeature = correspondingFeature;
		description = null;
		status = FeatureStatus.NORMAL;
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
	@CheckForNull
	public String getDescription() {
		return description.toString();
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
	public FeatureStatus getFeatureStatus() {
		return status;
	}

	@Override
	public void setDescription(CharSequence description) {
		this.description = description;
	}

	@Override
	public void setDisplayName(CharSequence name) {
	}

	@Override
	public void setFeatureStatus(FeatureStatus status) {
		this.status = status;
	}

	@Override
	public void setFeatureStatus(FeatureStatus stat, boolean fire) {
		this.status = stat;
		if (fire) {
			correspondingFeature.fireEvent(new PropertyChangeEvent(this, ATTRIBUTE_CHANGED, Boolean.FALSE, Boolean.TRUE));
		}
	}

	@Override
	public boolean isConstraintSelected() {
		throw new UnsupportedOperationException("Not implemented yet");
	}

	@Override
	public boolean selectConstraint(boolean state) {
		throw new UnsupportedOperationException("Not implemented yet");
	}

}
