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
package de.ovgu.featureide.fm.ui.editors.elements;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.impl.Constraint;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.Legend;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.FeatureModelLayout;

/**
 * Graphical representation of an {@link IFeatureModel} instance.
 *
 * @author Sebastian Krieter
 *
 */
public class GraphicalFeatureModel implements IGraphicalFeatureModel {

	protected final IFeatureModel correspondingFeatureModel;

	protected final FeatureModelLayout layout;

	protected Map<IFeature, IGraphicalFeature> features;
	protected Map<IConstraint, IGraphicalConstraint> constraints;

	protected boolean hiddenLegend;
	protected Legend legend;

	/**
	 * The currently active explanation that is shown in the FeatureDiagrammEditor if any defect element is selected.
	 */
	public Explanation<?> currentlyActiveExplanation = null;

	public GraphicalFeatureModel(IFeatureModel correspondingFeatureModel) {
		this.correspondingFeatureModel = correspondingFeatureModel;
		layout = new FeatureModelLayout();
	}

	/**
	 * Copy constructor
	 */
	protected GraphicalFeatureModel(GraphicalFeatureModel oldModel) {
		correspondingFeatureModel = oldModel.correspondingFeatureModel;

		layout = oldModel.layout;
		features = new HashMap<>((int) (correspondingFeatureModel.getNumberOfFeatures() * 1.5));
		for (final IGraphicalFeature feature : oldModel.features.values()) {
			features.put(feature.getObject(), feature.clone());
		}
		constraints = new HashMap<>((int) (correspondingFeatureModel.getConstraintCount() * 1.5));
		for (final Entry<IConstraint, IGraphicalConstraint> constraint : oldModel.constraints.entrySet()) {
			constraints.put(constraint.getKey(), constraint.getValue().clone());
		}
	}

	protected void fireEvent(final EventType action) {
		correspondingFeatureModel.fireEvent(new FeatureIDEEvent(this, action, Boolean.FALSE, Boolean.TRUE));
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
		fireEvent(EventType.LEGEND_LAYOUT_CHANGED);
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel#getLegendHidden()
	 */
	@Override
	public boolean isLegendHidden() {
		return hiddenLegend;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel#setLegendHidden(boolean)
	 */
	@Override
	public void setLegendHidden(boolean hidden) {
		hiddenLegend = hidden;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel#getLegend()
	 */
	@Override
	public Legend getLegend() {
		return legend;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel#setLegend(de.ovgu.featureide.fm.ui.editors.featuremodel.Legend)
	 */
	@Override
	public void setLegend(Legend legend) {
		this.legend = legend;
	}

	@Override
	public void handleModelLayoutChanged() {
		fireEvent(EventType.MODEL_LAYOUT_CHANGED);
	}

	@Override
	public void redrawDiagram() {
		fireEvent(EventType.REDRAW_DIAGRAM);
	}

	@Override
	public void refreshContextMenu() {
		fireEvent(EventType.REFRESH_ACTIONS);
	}

	@Override
	public Collection<IGraphicalFeature> getFeatures() {
		final ArrayList<IGraphicalFeature> featureList = new ArrayList<>(correspondingFeatureModel.getNumberOfFeatures());
		for (final IFeature f : correspondingFeatureModel.getVisibleFeatures(getLayout().showHiddenFeatures())) {
			featureList.add(getGraphicalFeature(f));
		}
		return Collections.unmodifiableCollection(featureList);
	}

	@Override
	public Collection<IGraphicalFeature> getAllFeatures() {
		final ArrayList<IGraphicalFeature> featureList = new ArrayList<>(correspondingFeatureModel.getNumberOfFeatures());
		for (final IFeature f : correspondingFeatureModel.getFeatures()) {
			featureList.add(getGraphicalFeature(f));
		}
		return Collections.unmodifiableCollection(featureList);
	}

	@Override
	public IGraphicalFeature getGraphicalFeature(IFeature newFeature) {
		IGraphicalFeature graphicalFeature = features.get(newFeature);
		if (graphicalFeature == null) {
			graphicalFeature = new GraphicalFeature(newFeature, this);
			features.put(newFeature, graphicalFeature);
		}
		return graphicalFeature;
	}

	@Override
	public List<IGraphicalConstraint> getConstraints() {
		final ArrayList<IGraphicalConstraint> constraintList = new ArrayList<>(correspondingFeatureModel.getConstraintCount());
		for (final IConstraint c : correspondingFeatureModel.getConstraints()) {
			constraintList.add(getGraphicalConstraint(c));
		}
		return constraintList;
	}

	@Override
	public List<IGraphicalConstraint> getVisibleConstraints() {
		if (getLayout().showCollapsedConstraints()) {
			return getConstraints();
		}
		final List<IGraphicalConstraint> constraints = new ArrayList<IGraphicalConstraint>();
		for (final IGraphicalConstraint c : getConstraints()) {
			if (!c.isCollapsed()) {
				constraints.add(c);
			}
		}
		return Collections.unmodifiableList(constraints);
	}

	@Override
	public IGraphicalConstraint getGraphicalConstraint(IConstraint constraint) {
		IGraphicalConstraint graphicalConstraint = constraints.get(constraint);
		if (graphicalConstraint == null) {
			graphicalConstraint = new GraphicalConstraint(constraint, this);
			constraints.put(constraint, graphicalConstraint);
		}
		return graphicalConstraint;
	}

	@Override
	public String toString() {
		if (features != null) {
			return "Graphical feature-model tree:\n" + features.toString();
		}
		return super.toString();
	}

	@Override
	public GraphicalFeatureModel clone() {
		final GraphicalFeatureModel copy = new GraphicalFeatureModel(this);
		return copy;
	}

	@Override
	public void init() {
		final IFeatureStructure root = correspondingFeatureModel.getStructure().getRoot();
		if (root != null) {
			constraints = new HashMap<>((int) (correspondingFeatureModel.getConstraintCount() * 1.5));
			for (final IConstraint constraint : correspondingFeatureModel.getConstraints()) {
				constraints.put(constraint, new GraphicalConstraint(constraint, this));
			}

			features = new HashMap<>((int) (correspondingFeatureModel.getNumberOfFeatures() * 1.5));
			for (final IFeature feature : correspondingFeatureModel.getVisibleFeatures(getLayout().showHiddenFeatures())) {
				features.put(feature, new GraphicalFeature(feature, this));
			}
		} else {
			constraints = new HashMap<>();
			features = new HashMap<>();
		}
	}

	@Override
	public List<IGraphicalFeature> getVisibleFeatures() {
		final List<IGraphicalFeature> features = new ArrayList<IGraphicalFeature>();
		for (final IGraphicalFeature f : getFeatures()) {
			if (!f.hasCollapsedParent()) {
				features.add(f);
			}
		}
		return Collections.unmodifiableList(features);
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel#getConstraintIndex(de.ovgu.featureide.fm.core.base.impl.Constraint)
	 */
	@Override
	public int getConstraintIndex(Constraint constraint) {
		final IGraphicalConstraint gConstarint = getGraphicalConstraint(constraint);

		int index = 0;
		for (int i = 0; i < constraints.size(); i++) {
			final IGraphicalConstraint gTemp = getGraphicalConstraint(getFeatureModel().getConstraints().get(i));
			if (gTemp == gConstarint) {
				return index;
			}

			if (!gTemp.isCollapsed()) {
				index++;
			}
		}
		return index;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel#setActiveExplanation(de.ovgu.featureide.fm.core.explanations.Explanation)
	 */
	@Override
	public void setActiveExplanation(Explanation<?> exp) {
		currentlyActiveExplanation = exp;

	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel#getActiveExplanation(de.ovgu.featureide.fm.core.explanations.Explanation)
	 */
	@Override
	public Explanation<?> getActiveExplanation() {
		// TODO Auto-generated method stub
		return currentlyActiveExplanation;
	}

}
