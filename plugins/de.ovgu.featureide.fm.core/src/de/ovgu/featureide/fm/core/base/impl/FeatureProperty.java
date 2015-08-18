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

import javax.annotation.CheckForNull;

import de.ovgu.featureide.fm.core.FeatureStatus;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureProperty;

/**
 * Provides all properties of a feature. This includes its connections to parent
 * and child features.
 * 
 * @author Thomas Thuem
 * @author Sebastian Krieter
 * 
 */
public class FeatureProperty implements IFeatureProperty {

	private final IFeature correspondingFeature;

	private String description;
	private FeatureStatus status;

	public FeatureProperty(IFeature correspondingFeature) {
		this.correspondingFeature = correspondingFeature;
		this.description = null;
		this.status = FeatureStatus.NORMAL;
	}
	
	public FeatureProperty(IFeatureProperty featureProperty) {
		this(featureProperty, featureProperty.getFeature());
	}
	
	public FeatureProperty(IFeatureProperty featureProperty, IFeature correspondingFeature) {
		this.correspondingFeature = correspondingFeature;
		this.description = new String(featureProperty.getDescription());
		this.status = featureProperty.getFeatureStatus();
	}

	/**
	 * 
	 * @return The description of the Feature.
	 */
	@CheckForNull
	public String getDescription() {
		return description;
	}

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
	public void setDescription(String description) {
		this.description = description;
	}

	@Override
	public void setDisplayName(String name) {
	}

	@Override
	public void setFeatureStatus(FeatureStatus status) {
		this.status = status;
	}

}
