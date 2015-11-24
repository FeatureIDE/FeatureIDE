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
import de.ovgu.featureide.fm.core.base.util.tree.Tree;
import de.ovgu.featureide.fm.ui.editors.FeatureConnection;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.IGraphicalElement;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * TODO description
 * 
 * @author Sebastian Krieter
 */
public final class GraphicMap {

	private static final GraphicMap INSTANCE = new GraphicMap();

	private HashMap<IFeatureModel, IGraphicalFeatureModel> modelMap = new HashMap<>();

	public static GraphicMap getInstance() {
		return INSTANCE;
	}

	private GraphicMap() {
	};

	public IGraphicalFeatureModel constructModel(IFeatureModel featureModel) {
		IGraphicalFeatureModel graphicalItem = modelMap.get(featureModel);
		boolean firstModel = graphicalItem == null;
		if (!firstModel) {
			final Tree<IGraphicalFeature> features = graphicalItem.getFeatures();
			final List<IGraphicalConstraint> constraints = graphicalItem.getConstraints();
			final HashMap<IFeatureModelElement, IGraphicalElement> map = new HashMap<>((int) ((constraints.size() + features.getNumberOfNodes()) * 1.5));
			for (IGraphicalFeature feature : features) {
				map.put(feature.getObject(), feature);
			}
			for (IGraphicalConstraint constraint : constraints) {
				map.put(constraint.getObject(), constraint);
			}

			graphicalItem = newModel(featureModel);

			for (IGraphicalFeature feature : graphicalItem.getFeatures()) {
				feature.copyValue(map.get(feature.getObject()));
			}
			for (IGraphicalConstraint constraint : graphicalItem.getConstraints()) {
				constraint.copyValue(map.get(constraint.getObject()));
			}
		} else {
			graphicalItem = newModel(featureModel);
		}

		modelMap.put(featureModel, graphicalItem);

		return graphicalItem;
	}

	/**
	 * @param featureModel
	 * @return
	 */
	private IGraphicalFeatureModel newModel(IFeatureModel featureModel) {
		IGraphicalFeatureModel graphicalItem;
		graphicalItem = new GraphicalFeatureModel(featureModel);

		final ArrayList<IGraphicalConstraint> constraintList = new ArrayList<>(featureModel.getConstraints().size());
		for (IConstraint constraint : featureModel.getConstraints()) {
			final IGraphicalConstraint graphicalFeature = new GraphicalConstraint(constraint, graphicalItem);
			constraintList.add(graphicalFeature);
		}
		graphicalItem.setConstraintList(constraintList);

		final IFeature rootFeature = featureModel.getStructure().getRoot().getFeature();

		final IGraphicalFeature graphicalFeature = new GraphicalFeature(rootFeature, graphicalItem);

		final Tree<IGraphicalFeature> rootTree = graphicalFeature.getTree();
		for (IFeatureStructure featureStructure : rootFeature.getStructure().getChildren()) {
			travers(rootTree, featureStructure.getFeature(), graphicalItem);
		}
		graphicalItem.setFeatureTree(rootTree);
		graphicalFeature.getSourceConnections().clear();
		return graphicalItem;
	}

	private void travers(Tree<IGraphicalFeature> rootTree, IFeature feature, IGraphicalFeatureModel graphicalItem) {
		final IGraphicalFeature graphicalFeature = new GraphicalFeature(feature, graphicalItem);
		Tree<IGraphicalFeature> subTree = graphicalFeature.getTree();
		rootTree.addSubTree(subTree);
		final FeatureConnection connection = graphicalFeature.getSourceConnections().get(0);
		rootTree.getObject().addTargetConnection(connection);
		for (IFeatureStructure featureStructure : feature.getStructure().getChildren()) {
			travers(subTree, featureStructure.getFeature(), graphicalItem);
		}
	}

	//	public IGraphicalFeature getGraphicRepresentation(IFeature feature) {
	//		IGraphicalFeature graphicalItem = featureMap.get(feature);
	//		if (graphicalItem == null) {
	//			graphicalItem = DefaultFeatureModelFactory.getInstance().createGraphicalRepresentation(feature);
	//			featureMap.put(feature, graphicalItem);
	//		}
	//		return graphicalItem;
	//	}
	//
	//	public IGraphicalConstraint getGraphicRepresentation(IConstraint constraint) {
	//		IGraphicalConstraint graphicalItem = constraintMap.get(constraint);
	//		if (graphicalItem == null) {
	//			graphicalItem = DefaultFeatureModelFactory.getInstance().createGraphicalRepresentation(constraint);
	//			constraintMap.put(constraint, graphicalItem);
	//		}
	//		return graphicalItem;
	//	}
	//
	//	public IGraphicalFeatureModel getGraphicRepresentation(IFeatureModel featureModel) {
	//		IGraphicalFeatureModel graphicalItem = modelMap.get(featureModel);
	//		if (graphicalItem == null) {
	//			graphicalItem = DefaultFeatureModelFactory.getInstance().createGraphicalRepresentation(featureModel);
	//			modelMap.put(featureModel, graphicalItem);
	//		}
	//		return graphicalItem;
	//	}

}
