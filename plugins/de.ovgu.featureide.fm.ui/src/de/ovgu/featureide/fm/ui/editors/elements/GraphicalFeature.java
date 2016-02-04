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
package de.ovgu.featureide.fm.ui.editors.elements;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.util.tree.Tree;
import de.ovgu.featureide.fm.ui.editors.FeatureConnection;
import de.ovgu.featureide.fm.ui.editors.IGraphicalElement;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Graphical representation of an {@link IFeature} instance.
 * 
 * @author Sebastian Krieter
 * 
 */
public class GraphicalFeature implements IGraphicalFeature {
	
	protected final FeatureConnection sourceConnection;

	protected boolean constraintSelected;
	
	protected IFeature feature;
	
	protected final IGraphicalFeatureModel graphicalFeatureModel;

	protected Tree<IGraphicalFeature> tree = new Tree<IGraphicalFeature>(this);

	protected Point location = new Point(0, 0);
	
	protected Dimension dimension = new Dimension(10, 10);

	public GraphicalFeature(IFeature correspondingFeature, IGraphicalFeatureModel graphicalFeatureModel) {
		this.graphicalFeatureModel = graphicalFeatureModel;
		this.feature = correspondingFeature;
		if (!correspondingFeature.getStructure().isRoot()) {
			sourceConnection = new FeatureConnection(this);
		} else {
			sourceConnection = null;
		}
	}

	@Override
	public IFeature getObject() {
		return feature;
	}

	@Override
	public GraphicItem getItemType() {
		return GraphicItem.Feature;
	}

	@Override
	public boolean isConstraintSelected() {
		return constraintSelected;
	}

	@Override
	public void setConstraintSelected(boolean selection) {
		constraintSelected = selection;
		feature.fireEvent(new FeatureIDEEvent(this, EventType.ATTRIBUTE_CHANGED, Boolean.FALSE, Boolean.TRUE));
	}

	@Override
	public Point getLocation() {
		return location;
	}
	
	@Override
	public void setLocation(Point newLocation) {
		if (!location.equals(newLocation)) {
			final FeatureIDEEvent event = new FeatureIDEEvent(this, EventType.LOCATION_CHANGED, location, newLocation);
			location = newLocation;
			feature.fireEvent(event);
		}
	}

	@Override
	public Dimension getSize() {
		return dimension;
	}

	@Override
	public void setSize(Dimension size) {
		this.dimension = size;
	}

	@Override
	public Tree<IGraphicalFeature> getTree() {
		return tree;
	}

	@Override
	public IGraphicalFeatureModel getGraphicalModel() {
		return graphicalFeatureModel;
	}

	@Override
	public void addTargetConnection(FeatureConnection connection) {
		
	}

	@Override
	public FeatureConnection getSourceConnection() {
		if (sourceConnection != null) {
			sourceConnection.setTarget(getTree().getParentObject());// XXX necessary?
		}
		return sourceConnection;
	}

	@Override
	public List<FeatureConnection> getSourceConnectionAsList() {
		final List<FeatureConnection> list;
		if (sourceConnection == null) {
			list = Collections.emptyList();
		} else {
			 list = new ArrayList<>(1);
			 list.add(getSourceConnection());
		}
		return Collections.unmodifiableList(list);
	}

	@Override
	public List<FeatureConnection> getTargetConnections() {
		final List<FeatureConnection> targetConnections = new LinkedList<>();
		for (IGraphicalFeature child : getTree().getChildrenObjects()) {
			targetConnections.add(child.getSourceConnection());
		}
		return Collections.unmodifiableList(targetConnections);
	}

	@Override
	public String toString() {
		return feature.toString();
	}

	@Override
	public String getGraphicType() {
		return "";
	}

	@Override
	public void copyValues(IGraphicalElement element) {
		if (element instanceof GraphicalFeature) {
			final GraphicalFeature oldFeature = (GraphicalFeature) element;

			constraintSelected = oldFeature.constraintSelected;
			location = oldFeature.location;
			dimension = oldFeature.dimension;
		}
	}

}
