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

	// TODO there is only one source/parent, why do we use a list
	protected final LinkedList<FeatureConnection> sourceConnections = new LinkedList<FeatureConnection>();
	protected final LinkedList<FeatureConnection> targetConnections = new LinkedList<FeatureConnection>();

	protected boolean constraintSelected;
	protected IFeature correspondingFeature;
	protected final IGraphicalFeatureModel graphicalFeatureModel;

	protected Tree<IGraphicalFeature> tree = new Tree<IGraphicalFeature>(this);

	protected Point location = new Point(0, 0);
	protected Dimension dimension = new Dimension(10, 10);

	public GraphicalFeature(IFeature correspondingFeature, IGraphicalFeatureModel graphicalFeatureModel) {
		this.correspondingFeature = correspondingFeature;
		this.graphicalFeatureModel = graphicalFeatureModel;

		sourceConnections.add(new FeatureConnection(this));
	}

	@Override
	public IFeature getObject() {
		return correspondingFeature;
	}

	@Override
	public GraphicItem getItemType() {
		return GraphicItem.Feature;
	}

	@Override
	public Point getLocation() {
		return location;
	}

	@Override
	public boolean isConstraintSelected() {
		return constraintSelected;
	}

	@Override
	public void setConstraintSelected(boolean selection) {
		constraintSelected = selection;
		correspondingFeature.fireEvent(new FeatureIDEEvent(this, EventType.ATTRIBUTE_CHANGED, Boolean.FALSE, Boolean.TRUE));
	}

	@Override
	public void setLocation(Point newLocation) {
		if (!location.equals(newLocation)) {
			final FeatureIDEEvent event = new FeatureIDEEvent(this, EventType.LOCATION_CHANGED, location, newLocation);
			location = newLocation;
			correspondingFeature.fireEvent(event);
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
		targetConnections.add(connection);
		connection.setTarget(this);
	}

	//	// delete old parent connection (if existing)
	//			if (parent != null) {
	//				parent.removeTargetConnection(parentConnection);
	//				parentConnection.setTarget(null);
	//			}
	//
	//			// update the target
	//			if (newParent != null) {
	//				parentConnection.setTarget(newParent.getFeature());
	//				newParent.addTargetConnection(parentConnection);
	//			}

	@Override
	public List<FeatureConnection> getSourceConnections() {
		return sourceConnections == null ? Collections.<FeatureConnection> emptyList() : sourceConnections;
	}

	@Override
	public List<FeatureConnection> getTargetConnections() {
		return targetConnections;
	}

	@Override
	public boolean removeTargetConnection(FeatureConnection connection) {
		return targetConnections.remove(connection);
	}

	@Override
	public String toString() {
		return correspondingFeature.toString();
	}

	@Override
	public String getGraphicType() {
		return null;
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
