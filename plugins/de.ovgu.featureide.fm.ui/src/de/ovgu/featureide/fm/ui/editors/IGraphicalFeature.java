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

import java.util.List;

import javax.annotation.CheckForNull;
import javax.annotation.Nonnull;

import de.ovgu.featureide.fm.core.base.IFeature;

/**
 * Graphical representation of a feature.
 *
 * @author Sebastian Krieter
 */
public interface IGraphicalFeature extends IGraphicalElement {

	@Override
	IFeature getObject();

	boolean isCollapsed();

	boolean isConstraintSelected();

	void setConstraintSelected(boolean selection);

	void setCollapsed(boolean collapse);

	void addTargetConnection(FeatureConnection connection);

	@CheckForNull
	FeatureConnection getSourceConnection();

	@Nonnull
	List<FeatureConnection> getSourceConnectionAsList();

	List<FeatureConnection> getTargetConnections();

	IGraphicalFeature clone();

	boolean hasCollapsedParent();

	List<IGraphicalFeature> getGraphicalChildren(boolean showHidden);

	List<IGraphicalFeature> getAllGraphicalChildren();

}
