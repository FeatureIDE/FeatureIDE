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
import java.util.HashMap;
import java.util.List;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureModelEvent;
import de.ovgu.featureide.fm.core.base.event.PropertyConstants;
import de.ovgu.featureide.fm.core.base.util.tree.Tree;
import de.ovgu.featureide.fm.ui.editors.FeatureConnection;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.IGraphicalElement;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.FeatureModelLayout;

/**
 * Graphical representation of an {@link IFeatureModel} instance.
 * 
 * @author Sebastian Krieter
 * @author Marcus Pinnecke
 * 
 */
public class GraphicalFeatureModel implements IGraphicalFeatureModel, PropertyConstants {

	protected final IFeatureModel correspondingFeatureModel;

	protected final FeatureModelLayout layout;

	protected Tree<IGraphicalFeature> featureTree = null;
	protected List<IGraphicalConstraint> constraintList = null;

	public GraphicalFeatureModel(IFeatureModel correspondingFeatureModel) {
		this.correspondingFeatureModel = correspondingFeatureModel;
		layout = new FeatureModelLayout();
	}

	private GraphicalFeatureModel(GraphicalFeatureModel oldModel) {
		this.correspondingFeatureModel = oldModel.correspondingFeatureModel;

		constraintList = oldModel.constraintList;
		layout = oldModel.layout;
	}

	protected void fireEvent(final String action) {
		correspondingFeatureModel.fireEvent(new FeatureModelEvent(this, action, Boolean.FALSE, Boolean.TRUE));
	}

	@Override
	public IFeatureModel getFeatureModel() {
		return correspondingFeatureModel;
	}

	@Override
	public GraphicItem getItemType() {
		return GraphicItem.Model;
	}

	@Override
	public FeatureModelLayout getLayout() {
		return layout;
	}

	@Override
	public void handleLegendLayoutChanged() {
		fireEvent(FeatureModelEvent.LEGEND_LAYOUT_CHANGED);
	}

	@Override
	public void handleModelLayoutChanged() {
		fireEvent(FeatureModelEvent.MODEL_LAYOUT_CHANGED);
	}

	@Override
	public void redrawDiagram() {
		fireEvent(REDRAW_DIAGRAM);
	}

	@Override
	public void refreshContextMenu() {
		fireEvent(REFRESH_ACTIONS);
	}

	public Tree<IGraphicalFeature> getFeatures() {
		return featureTree;
	}

	public void setFeatureTree(Tree<IGraphicalFeature> featureTree) {
		this.featureTree = featureTree;
	}

	public List<IGraphicalConstraint> getConstraints() {
		return constraintList;
	}

	public void setConstraintList(List<IGraphicalConstraint> constraintList) {
		this.constraintList = constraintList;
	}

	@Override
	public IGraphicalFeature getGraphicalFeature(IFeature newFeature) {
		for (IGraphicalFeature graphicalFeature : featureTree) {
			if (graphicalFeature.getObject().equals(newFeature)) {
				return graphicalFeature;
			}
		}
		return null;
	}

	@Override
	public String toString() {
		if (featureTree != null) {
			return "Graphical feature-model tree:\n" + featureTree.toString();
		}
		return super.toString();
	}

	public void update() {
		final HashMap<IFeatureModelElement, IGraphicalElement> map = createElementMap();

		init();

		update(map, this);
	}

	public GraphicalFeatureModel clone() {
		final HashMap<IFeatureModelElement, IGraphicalElement> map = createElementMap();

		final GraphicalFeatureModel copy = new GraphicalFeatureModel(this);
		copy.init();

		update(map, copy);
		return copy;
	}

	private void update(final HashMap<IFeatureModelElement, IGraphicalElement> map, final GraphicalFeatureModel model) {
		for (IGraphicalFeature feature : model.featureTree) {
			feature.copyValues(map.get(feature.getObject()));
		}
		for (IGraphicalConstraint constraint : model.constraintList) {
			constraint.copyValues(map.get(constraint.getObject()));
		}
	}

	private HashMap<IFeatureModelElement, IGraphicalElement> createElementMap() {
		final HashMap<IFeatureModelElement, IGraphicalElement> map = new HashMap<>((int) ((constraintList.size() + featureTree.getNumberOfNodes()) * 1.5));
		for (IGraphicalFeature feature : featureTree) {
			map.put(feature.getObject(), feature);
		}
		for (IGraphicalConstraint constraint : constraintList) {
			map.put(constraint.getObject(), constraint);
		}
		return map;
	}

	public void init() {
		final ArrayList<IGraphicalConstraint> constraintList = new ArrayList<>(correspondingFeatureModel.getConstraints().size());
		for (IConstraint constraint : correspondingFeatureModel.getConstraints()) {
			final IGraphicalConstraint graphicalFeature = new GraphicalConstraint(constraint, this);
			constraintList.add(graphicalFeature);
		}

		final IFeature rootFeature = correspondingFeatureModel.getStructure().getRoot().getFeature();

		final IGraphicalFeature graphicalFeature = new GraphicalFeature(rootFeature, this);

		final Tree<IGraphicalFeature> rootTree = graphicalFeature.getTree();
		for (IFeatureStructure featureStructure : rootFeature.getStructure().getChildren()) {
			traverse(rootTree, featureStructure.getFeature(), this);
		}
		graphicalFeature.getSourceConnections().clear();

		this.constraintList = constraintList;
		this.featureTree = rootTree;
	}

	private static void traverse(Tree<IGraphicalFeature> rootTree, IFeature feature, IGraphicalFeatureModel graphicalItem) {
		final IGraphicalFeature graphicalFeature = new GraphicalFeature(feature, graphicalItem);
		Tree<IGraphicalFeature> subTree = graphicalFeature.getTree();
		rootTree.addSubTree(subTree);
		final FeatureConnection connection = graphicalFeature.getSourceConnections().get(0);
		rootTree.getObject().addTargetConnection(connection);
		for (IFeatureStructure featureStructure : feature.getStructure().getChildren()) {
			traverse(subTree, featureStructure.getFeature(), graphicalItem);
		}
	}

}
