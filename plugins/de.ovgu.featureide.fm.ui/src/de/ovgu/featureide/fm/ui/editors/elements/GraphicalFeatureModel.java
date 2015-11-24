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

import java.util.List;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureModelEvent;
import de.ovgu.featureide.fm.core.base.event.PropertyConstants;
import de.ovgu.featureide.fm.core.base.impl.Tree;
import de.ovgu.featureide.fm.ui.ColorschemeTable;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
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

	protected final ColorschemeTable colorschemeTable;

	protected final IFeatureModel correspondingFeatureModel;

	protected Tree<IGraphicalFeature> featureTree = null;
	protected List<IGraphicalConstraint> constraintList = null;

	protected final FeatureModelLayout layout;

	public GraphicalFeatureModel(IFeatureModel correspondingFeatureModel) {
		this.correspondingFeatureModel = correspondingFeatureModel;
		layout = new FeatureModelLayout();
		colorschemeTable = new ColorschemeTable(this);
	}

	protected void fireEvent(final String action) {
		correspondingFeatureModel.fireEvent(new FeatureModelEvent(this, action, Boolean.FALSE, Boolean.TRUE));
	}

	@Override
	public ColorschemeTable getColorschemeTable() {
		return colorschemeTable;
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
		fireEvent(LEGEND_LAYOUT_CHANGED);
	}

	@Override
	public void handleModelLayoutChanged() {
		fireEvent(MODEL_LAYOUT_CHANGED);
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

}
