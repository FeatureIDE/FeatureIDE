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
package de.ovgu.featureide.fm.core.base.impl;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.base.event.DefaultEventManager;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.event.IEventManager;

/**
 * Partial implementation of feature and constraint.
 *
 * @author Sebastian Krieter
 *
 */
public abstract class AFeatureModelElement implements IFeatureModelElement {

	protected final long id;

	protected String name;

	protected final IFeatureModel featureModel;
	protected final IEventManager eventManager = new DefaultEventManager();

	protected AFeatureModelElement(AFeatureModelElement oldElement, IFeatureModel featureModel) {
		this.featureModel = featureModel != null ? featureModel : oldElement.featureModel;
		id = oldElement.id;
		name = (oldElement.name == null) ? null : new String(oldElement.name);
	}

	public AFeatureModelElement(IFeatureModel featureModel) {
		if (featureModel == null) {
			throw new RuntimeException();
		}
		id = featureModel.getNextElementId();
		this.featureModel = featureModel;
		name = null;
	}

	@Override
	public IFeatureModel getFeatureModel() {
		return featureModel;
	}

	@Override
	public final long getInternalId() {
		return id;
	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public void setName(String name) {
		this.name = name;
	}

	@Override
	public final void addListener(IEventListener listener) {
		eventManager.addListener(listener);
	}

	@Override
	public final void removeListener(IEventListener listener) {
		eventManager.removeListener(listener);
	}

	@Override
	public final void fireEvent(FeatureIDEEvent event) {
		eventManager.fireEvent(event);
	}

	@Override
	public final int hashCode() {
		return (int) (37 * id);
	}

	@Override
	public final boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if ((obj == null) || (getClass() != obj.getClass())) {
			return false;
		}
		final AFeatureModelElement other = (AFeatureModelElement) obj;
		return id == other.id;
	}

}
