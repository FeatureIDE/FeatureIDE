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
package de.ovgu.featureide.fm.ui.editors;

import de.ovgu.featureide.fm.core.IGraphicItem;

/**
 * An instance of this class represents a connection between a feature and its parent. It is necessary because every figure in GEF needs a associated model.
 *
 * @author Thomas Thuem
 *
 */
public class FeatureConnection implements IGraphicItem {

	private final IGraphicalFeature source;
	private IGraphicalFeature target;

	public FeatureConnection(IGraphicalFeature source) {
		this.source = source;
	}

	public IGraphicalFeature getSource() {
		return source;
	}

	public IGraphicalFeature getTarget() {
		return target;
	}

	public void setTarget(IGraphicalFeature target) {
		this.target = target;
	}

	@Override
	public String toString() {
		return source + " - " + target;
	}

	@Override
	public GraphicItem getItemType() {
		return GraphicItem.Connection;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = (prime * result) + ((source == null) ? 0 : source.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final FeatureConnection other = (FeatureConnection) obj;
		if (source == null) {
			if (other.source != null) {
				return false;
			}
		} else if (!source.equals(other.source)) {
			return false;
		}
		if (target == null) {
			if (other.target != null) {
				return false;
			}
		} else if (!target.equals(other.target)) {
			return false;
		}
		return true;
	}
}
