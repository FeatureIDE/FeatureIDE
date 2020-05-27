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
package de.ovgu.featureide.fm.ui.editors.elements;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.ui.editors.FeatureConnection;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.CollapsedDecoration;

/**
 * Graphical representation of an {@link IFeature} instance.
 *
 * @author Sebastian Krieter
 *
 */
public class GraphicalFeature implements IGraphicalFeature {

	protected final FeatureConnection sourceConnection;

	protected boolean constraintSelected;

	protected IFeature featureObject;

	protected final IGraphicalFeatureModel graphicalFeatureModel;

	protected boolean collapsed;

	protected Point location = new Point(0, 0);

	protected Dimension dimension = new Dimension(10, 10);

	private IEventListener uiObject;

	private CollapsedDecoration deco;

	public GraphicalFeature(IFeature correspondingFeature, IGraphicalFeatureModel graphicalFeatureModel) {
		this.graphicalFeatureModel = graphicalFeatureModel;
		featureObject = correspondingFeature;
		sourceConnection = new FeatureConnection(this);
	}

	public GraphicalFeature(GraphicalFeature graphicalFeature) {
		collapsed = graphicalFeature.collapsed;
		constraintSelected = graphicalFeature.constraintSelected;
		location = graphicalFeature.location;
		dimension = graphicalFeature.dimension;
		featureObject = graphicalFeature.featureObject;
		graphicalFeatureModel = graphicalFeature.graphicalFeatureModel;
		sourceConnection = graphicalFeature.sourceConnection;
	}

	@Override
	public IFeature getObject() {
		final IFeatureModelElement element = graphicalFeatureModel.getFeatureModelManager().getVarObject().getElement(featureObject.getInternalId());
		return element instanceof IFeature ? (IFeature) element : featureObject;
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
		if (constraintSelected != selection) {
			constraintSelected = selection;
			update(FeatureIDEEvent.getDefault(EventType.ATTRIBUTE_CHANGED));
		}
	}

	@Override
	public Point getLocation() {
		return location;
	}

	@Override
	public void setLocation(Point newLocation) {
		if (!location.equals(newLocation)) {
			location = newLocation;
			update(FeatureIDEEvent.getDefault(EventType.LOCATION_CHANGED));
		}
	}

	@Override
	public Dimension getSize() {
		return dimension;
	}

	@Override
	public void setSize(Dimension size) {
		dimension = size;
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
		sourceConnection.setTarget(FeatureUIHelper.getGraphicalParent(getObject(), graphicalFeatureModel));
		return sourceConnection;
	}

	@Override
	public List<FeatureConnection> getSourceConnectionAsList() {
		final List<FeatureConnection> list;
		list = new LinkedList<>();
		list.add(getSourceConnection());
		if (isCollapsed()) {
			final FeatureConnection collapsedConnection = new FeatureConnection(this);
			collapsedConnection.setTarget(this);
			list.add(collapsedConnection);
		}
		return (list);
	}

	@Override
	public List<FeatureConnection> getTargetConnections() {
		final List<FeatureConnection> targetConnections = new LinkedList<>();
		for (final IFeatureStructure child : getObject().getStructure().getChildren()) {
			final IGraphicalFeature graphicalChild = graphicalFeatureModel.getGraphicalFeature(child.getFeature());
			if (!graphicalChild.hasCollapsedParent()) {
				targetConnections.add(FeatureUIHelper.getGraphicalFeature(child, graphicalFeatureModel).getSourceConnection());
			}
		}
		return targetConnections;
	}

	@Override
	public String toString() {
		final IFeature feature = getObject();
		if (feature != null) {
			return feature.toString();
		} else {
			return "";
		}
	}

	@Override
	public String getGraphicType() {
		return "";
	}

	@Override
	public GraphicalFeature clone() {
		return new GraphicalFeature(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		return (int) (prime * featureObject.getInternalId());
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if ((obj == null) || !(obj instanceof GraphicalFeature)) {
			return false;
		}
		final GraphicalFeature other = (GraphicalFeature) obj;
		return featureObject.getInternalId() == other.featureObject.getInternalId();
	}

	@Override
	public void update(FeatureIDEEvent event) {
		if (uiObject != null) {
			uiObject.propertyChange(event);
		}
	}

	@Override
	public void registerUIObject(IEventListener listener) {
		uiObject = listener;
	}

	@Override
	public void deregisterUIObject() {
		uiObject = null;
	}

	@Override
	public boolean isCollapsed() {
		if (!getObject().getStructure().hasChildren()) {
			return false;
		}
		return collapsed;
	}

	@Override
	public void setCollapsed(boolean collapse) {
		collapsed = collapse;
	}

	@Override
	public boolean hasCollapsedParent() {
		IFeatureStructure parent = getObject().getStructure().getParent();
		if (parent == null) {
			return false;
		}

		while (parent != null) {
			final IGraphicalFeature graphicParent = getGraphicalModel().getGraphicalFeature(parent.getFeature());

			if (graphicParent.isCollapsed()) {
				return true;
			}

			parent = parent.getFeature().getStructure().getParent();
		}
		return false;
	}

	@Override
	public List<IGraphicalFeature> getGraphicalChildren() {
		final List<IGraphicalFeature> features = new ArrayList<>();
		for (final IFeatureStructure f : getObject().getStructure().getChildren()) {
			final IGraphicalFeature gf = getGraphicalModel().getGraphicalFeature(f.getFeature());
			if (!gf.hasCollapsedParent()) {
				features.add(gf);
			}
		}
		return Collections.unmodifiableList(features);
	}

	@Override
	public void setCollapsedDecoration(CollapsedDecoration decoration) {
		deco = decoration;
	}

	@Override
	public CollapsedDecoration getCollapsedDecoration() {
		return deco;
	}

	@Override
	public List<IGraphicalFeature> getAllGraphicalChildren() {
		final List<IGraphicalFeature> features = new ArrayList<IGraphicalFeature>();
		for (final IFeatureStructure f : getObject().getStructure().getChildren()) {
			final IGraphicalFeature gf = getGraphicalModel().getGraphicalFeature(f.getFeature());
			features.add(gf);
		}
		return features;
	}

}
