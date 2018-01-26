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
package de.ovgu.featureide.fm.attributes.base;

import de.ovgu.featureide.fm.core.base.IFeature;

/**
 * TODO description
 *
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public interface IFeatureAttribute {

	public IFeature getFeature();

	public String getName();

	public String getUnit();

	public Object getValue();

	public String getType();

	public boolean isRecursive();

	public boolean isConfigurable();

	public void setName(String name);

	public void setUnit(String unit);

	public void setValue(Object value);

	public void setRecursive(boolean recursive);

	public void setConfigureable(boolean configureable);

	public void recurseAttribute(IFeature feature);

	public void deleteRecursiveAttributes(IFeature feature);

	public void setFeature(IFeature feature);

	public IFeatureAttribute cloneRecursive(IFeature feature);

	public IFeatureAttribute cloneAtt(IFeature feature);

	public boolean isHeadOfRecursiveAttribute();
}
