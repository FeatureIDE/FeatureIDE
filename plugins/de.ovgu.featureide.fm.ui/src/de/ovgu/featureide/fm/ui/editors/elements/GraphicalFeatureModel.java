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
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.IPropertyContainer;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.impl.Constraint;
import de.ovgu.featureide.fm.core.base.impl.FeatureModelProperty;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.IGraphicalElement;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.Legend;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.FeatureModelLayout;

/**
 * Graphical representation of an {@link IFeatureModel} instance.
 *
 * @author Sebastian Krieter
 * @author Rahel Arens
 * @author Thomas Graave
 *
 */
public class GraphicalFeatureModel implements IGraphicalFeatureModel {

	protected final IFeatureModelManager featureModelManager;

	protected final FeatureModelLayout layout;

	protected Map<IFeature, IGraphicalFeature> features = new HashMap<>();
	protected Map<IConstraint, IGraphicalConstraint> constraints = new HashMap<>();

	protected boolean hiddenLegend = false;
	protected boolean hiddenConstraints = false;
	protected Legend legend;

	/**
	 * The currently active explanation that is shown in the FeatureDiagrammEditor if any defect element is selected.
	 */
	public Explanation<?> currentlyActiveExplanation = null;

	public GraphicalFeatureModel(IFeatureModelManager featureModelManager) {
		this.featureModelManager = featureModelManager;
		layout = new FeatureModelLayout();
		legend = new Legend(this);
	}

	/**
	 * Copy constructor
	 */
	protected GraphicalFeatureModel(GraphicalFeatureModel oldModel) {
		featureModelManager = oldModel.featureModelManager;
		layout = oldModel.layout;
		hiddenLegend = oldModel.hiddenLegend;
		legend = oldModel.legend;

		features = new HashMap<>((int) (oldModel.features.size() * 1.5));
		for (final IGraphicalFeature feature : oldModel.features.values()) {
			features.put(feature.getObject(), feature.clone());
		}

		constraints = new HashMap<>((int) (oldModel.constraints.size() * 1.5));
		for (final Entry<IConstraint, IGraphicalConstraint> constraint : oldModel.constraints.entrySet()) {
			constraints.put(constraint.getKey(), constraint.getValue().clone());
		}
	}

	protected void fireEvent(final EventType action) {
		featureModelManager.fireEvent(new FeatureIDEEvent(this, action, Boolean.FALSE, Boolean.TRUE));
	}

	@Override
	public IFeatureModelManager getFeatureModelManager() {
		return featureModelManager;
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

	@Override
	public boolean isLegendHidden() {
		return hiddenLegend;
	}

	@Override
	public void setLegendHidden(boolean hidden) {
		hiddenLegend = hidden;
	}

	@Override
	public Legend getLegend() {
		return legend;
	}

	@Override
	public void setConstraintsHidden(boolean hideConstraints) {
		hiddenConstraints = hideConstraints;
	}

	@Override
	public boolean getConstraintsHidden() {
		return hiddenConstraints;
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
		final IFeatureModel featureModel = featureModelManager.getSnapshot();
		final ArrayList<IGraphicalFeature> featureList = new ArrayList<>(featureModel.getNumberOfFeatures());
		for (final IFeature f : featureModel.getVisibleFeatures()) {
			featureList.add(getGraphicalFeature(f));
		}
		return Collections.unmodifiableCollection(featureList);
	}

	@Override
	public Collection<IGraphicalFeature> getAllFeatures() {
		final IFeatureModel featureModel = featureModelManager.getSnapshot();
		final ArrayList<IGraphicalFeature> featureList = new ArrayList<>(featureModel.getNumberOfFeatures());
		for (final IFeature f : featureModel.getFeatures()) {
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

	public IGraphicalFeature removeGraphicalFeature(IFeature feature) {
		return features.remove(feature);
	}

	@Override
	public List<IGraphicalConstraint> getConstraints() {
		final IFeatureModel featureModel = featureModelManager.getSnapshot();
		final ArrayList<IGraphicalConstraint> constraintList = new ArrayList<>(featureModel.getConstraintCount());
		for (final IConstraint c : featureModel.getConstraints()) {
			constraintList.add(getGraphicalConstraint(c));
		}
		return constraintList;
	}

	@Override
	public List<IGraphicalConstraint> getVisibleConstraints() {
		final List<IGraphicalConstraint> constraints = new ArrayList<IGraphicalConstraint>();
		if (hiddenConstraints) {
			return constraints;
		}
		return getNonCollapsedConstraints();
	}

	@Override
	public List<IGraphicalConstraint> getNonCollapsedConstraints() {
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
		final IFeatureModel featureModel = featureModelManager.getSnapshot();
		final IFeatureStructure root = featureModel.getStructure().getRoot();
		if (root != null) {
			constraints = new HashMap<>((int) (featureModel.getConstraintCount() * 1.5));
			for (final IConstraint constraint : featureModel.getConstraints()) {
				constraints.put(constraint, new GraphicalConstraint(constraint, this));
			}

			features = new HashMap<>((int) (featureModel.getNumberOfFeatures() * 1.5));
			for (final IFeature feature : featureModel.getVisibleFeatures()) {
				features.put(feature, new GraphicalFeature(feature, this));
			}
		} else {
			constraints = new HashMap<>();
			features = new HashMap<>();
		}
		readValues();
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

	@Override
	public List<IGraphicalFeature> getVisibleRelations() {
		final List<IGraphicalFeature> features = new ArrayList<IGraphicalFeature>();
		for (final IGraphicalFeature f : getFeatures()) {
			if (!f.isCollapsed() && !f.hasCollapsedParent()) {
				features.add(f);
			}
		}
		return Collections.unmodifiableList(features);
	}

	@Override
	public int getConstraintIndex(Constraint constraint) {
		final IGraphicalConstraint gConstarint = getGraphicalConstraint(constraint);

		int index = 0;
		for (int i = 0; i < constraints.size(); i++) {
			final IGraphicalConstraint gTemp = getGraphicalConstraint(featureModelManager.getSnapshot().getConstraints().get(i));
			if (gTemp == gConstarint) {
				return index;
			}

			if (!gTemp.isCollapsed()) {
				index++;
			}
		}
		return index;
	}

	@Override
	public void setActiveExplanation(Explanation<?> exp) {
		currentlyActiveExplanation = exp;
	}

	@Override
	public Explanation<?> getActiveExplanation() {
		return currentlyActiveExplanation;
	}

	private static final String LAYOUT_ALGORITHM = "layoutalgorithm";
	private static final String SHOW_COLLAPSED_CONSTRAINTS = "showcollapsedconstraints";
	private static final String SHOW_SHORT_NAMES = "showshortnames";
	private static final String LEGEND_AUTO_LAYOUT = "legendautolayout";
	private static final String LEGEND_HIDDEN = "legendhidden";
	private static final String LEGEND_POSITION = "legendposition";
	private static final String LAYOUT = "layout";
	private static final String POSITION = "position";
	private static final String COLLAPSED = "collapsed";

	private static final String VALUE_VERTICAL = "vertical";
	private static final String VALUE_HORIZONTAL = "horizontal";

	private static final String TYPE_GRAPHICS = "graphics";

	@Override
	public void readValues() {
		final IFeatureModel fm = featureModelManager.getSnapshot();

		getLayout().setLayout(Integer.parseInt(fm.getProperty().get(LAYOUT_ALGORITHM, TYPE_GRAPHICS, "1")));

		switch (fm.getProperty().get(LAYOUT, TYPE_GRAPHICS, VALUE_HORIZONTAL)) {
		case VALUE_VERTICAL:
			getLayout().setVerticalLayout(true);
		case VALUE_HORIZONTAL:
		default:
			getLayout().setVerticalLayout(false);
		}

		final Boolean shortNames = FeatureModelProperty.getBooleanProperty(fm.getProperty(), TYPE_GRAPHICS, SHOW_SHORT_NAMES);
		getLayout().setShowShortNames(shortNames != null ? shortNames : false);

		final Boolean colapsedConstraints = FeatureModelProperty.getBooleanProperty(fm.getProperty(), TYPE_GRAPHICS, SHOW_COLLAPSED_CONSTRAINTS);
		getLayout().showCollapsedConstraints(colapsedConstraints != null ? colapsedConstraints : true);

		final Boolean legendHidden = FeatureModelProperty.getBooleanProperty(fm.getProperty(), TYPE_GRAPHICS, LEGEND_HIDDEN);
		setLegendHidden(legendHidden != null ? legendHidden : false);

		final Boolean legendAutoLayout = FeatureModelProperty.getBooleanProperty(fm.getProperty(), TYPE_GRAPHICS, LEGEND_AUTO_LAYOUT);
		getLayout().setLegendAutoLayout(legendAutoLayout != null ? legendAutoLayout : true);

		if (!getLayout().hasLegendAutoLayout()) {
			final Point legendPos = new Point();
			final int[] coordinates = convertCoordinatesString(fm.getProperty().get(LEGEND_POSITION, TYPE_GRAPHICS, "0,0"), 2);
			legendPos.x = coordinates[0];
			legendPos.y = coordinates[1];
			getLegend().setPos(legendPos);
		}

		final boolean manualLayout = !getLayout().hasFeaturesAutoLayout();
		for (final IGraphicalFeature graphicalFeature : getAllFeatures()) {
			final IFeature feature = graphicalFeature.getObject();
			if (feature != null) {
				final IPropertyContainer customProperties = feature.getCustomProperties();
				if (manualLayout) {
					final Point location = new Point();
					final int[] coordinates = convertCoordinatesString(customProperties.get(POSITION, TYPE_GRAPHICS, "0,0"), 2);
					location.x = coordinates[0];
					location.y = coordinates[1];
					graphicalFeature.setLocation(location);
				}

				final Boolean isCollapsed = FeatureModelProperty.getBooleanProperty(customProperties, TYPE_GRAPHICS, COLLAPSED);
				if (isCollapsed == null) {
//					//Write default value
					if (getAllFeatures().size() < FeatureModelProperty.BIG_MODEL_LIMIT) {
						// Small model => no collapse
						graphicalFeature.setCollapsed(false);
					} else {
						// big model => collapse but root
						graphicalFeature.setCollapsed(!feature.getStructure().isRoot());
					}
				} else {
					graphicalFeature.setCollapsed(isCollapsed);
				}
			}
		}
		for (final IGraphicalConstraint constr : getConstraints()) {
			final IConstraint constraint = constr.getObject();
			if (constraint != null) {
				final IPropertyContainer customProperties = constraint.getCustomProperties();
				if (manualLayout) {
					final Point location = new Point();
					final int[] coordinates = convertCoordinatesString(customProperties.get(POSITION, TYPE_GRAPHICS, "0,0"), 2);
					location.x = coordinates[0];
					location.y = coordinates[1];
					constr.setLocation(location);
				}
			}
		}
	}

	private int[] convertCoordinatesString(final String coordinatesString, int dimensions) {
		final String[] coordinates = coordinatesString.split(",");
		if (coordinates.length != dimensions) {
			throw new NumberFormatException(coordinatesString);
		}
		final int[] c = new int[dimensions];
		for (int i = 0; i < dimensions; i++) {
			c[i] = Integer.parseInt(coordinates[i]);
		}
		return c;
	}

	@Override
	public void writeValues() {
		featureModelManager.editObject(this::writeElementsInternal, FeatureModelManager.CHANGE_GRAPHICS);
	}

	private void writeElementsInternal(final IFeatureModel fm) {
		writeFeatureModelInternal(fm);
		for (final IGraphicalFeature graphicalFeature : getAllFeatures()) {
			writeFeatureInternal(fm, graphicalFeature);
		}
		for (final IGraphicalConstraint graphicalConstraint : getConstraints()) {
			writeConstraintInternal(graphicalConstraint);
		}
	}

	@Override
	public void writeFeatureModel() {
		featureModelManager.editObject(this::writeFeatureModelInternal, FeatureModelManager.CHANGE_GRAPHICS);
	}

	@Override
	public void writeConstraint(final IGraphicalConstraint graphicalConstraint) {
		featureModelManager.editObject(fm -> writeConstraintInternal(graphicalConstraint), FeatureModelManager.CHANGE_GRAPHICS);
	}

	@Override
	public void writeFeature(final IGraphicalFeature graphicalFeature) {
		featureModelManager.editObject(fm -> writeFeatureInternal(fm, graphicalFeature), FeatureModelManager.CHANGE_GRAPHICS);
	}

	private void writeFeatureModelInternal(IFeatureModel fm) {
		writeLayoutAlgorithm(fm);
		writeAttributes(fm);
		writeLegend(fm);
	}

	private void writeConstraintInternal(final IGraphicalConstraint graphicalConstraint) {
		writePosition(graphicalConstraint, graphicalConstraint.getObject().getCustomProperties());
	}

	private void writeFeatureInternal(final IFeatureModel fm, final IGraphicalFeature graphicalFeature) {
		final IPropertyContainer customProperties = fm.getFeature(graphicalFeature.getObject().getName()).getCustomProperties();
		writePosition(graphicalFeature, customProperties);
		if (graphicalFeature.isCollapsed()) {
			customProperties.set(COLLAPSED, TYPE_GRAPHICS, FeatureModelProperty.VALUE_BOOLEAN_TRUE);
		} else if (customProperties.has(COLLAPSED, TYPE_GRAPHICS) || (fm.getNumberOfFeatures() >= FeatureModelProperty.BIG_MODEL_LIMIT)) {
			customProperties.set(COLLAPSED, TYPE_GRAPHICS, FeatureModelProperty.VALUE_BOOLEAN_FALSE);
		}
	}

	private void writePosition(final IGraphicalElement graphicalFeature, final IPropertyContainer customProperties) {
		if (getLayout().hasFeaturesAutoLayout()) {
			customProperties.remove(POSITION, TYPE_GRAPHICS);
		} else {
			final Point location = graphicalFeature.getLocation();
			customProperties.set(POSITION, TYPE_GRAPHICS, location.x + "," + location.y);
		}
	}

	private void writeAttributes(final IFeatureModel fm) {
		if (getLayout().showShortNames()) {
			fm.getProperty().set(SHOW_SHORT_NAMES, TYPE_GRAPHICS, FeatureModelProperty.VALUE_BOOLEAN_TRUE);
		} else {
			fm.getProperty().set(SHOW_SHORT_NAMES, TYPE_GRAPHICS, FeatureModelProperty.VALUE_BOOLEAN_FALSE);
		}
		if (getLayout().showCollapsedConstraints()) {
			fm.getProperty().set(SHOW_COLLAPSED_CONSTRAINTS, TYPE_GRAPHICS, FeatureModelProperty.VALUE_BOOLEAN_TRUE);
		} else {
			fm.getProperty().set(SHOW_COLLAPSED_CONSTRAINTS, TYPE_GRAPHICS, FeatureModelProperty.VALUE_BOOLEAN_FALSE);
		}
	}

	private void writeLegend(final IFeatureModel fm) {
		if (isLegendHidden()) {
			fm.getProperty().set(LEGEND_HIDDEN, TYPE_GRAPHICS, FeatureModelProperty.VALUE_BOOLEAN_TRUE);
		} else {
			fm.getProperty().set(LEGEND_HIDDEN, TYPE_GRAPHICS, FeatureModelProperty.VALUE_BOOLEAN_FALSE);
		}
		if (getLayout().hasLegendAutoLayout()) {
			fm.getProperty().set(LEGEND_AUTO_LAYOUT, TYPE_GRAPHICS, FeatureModelProperty.VALUE_BOOLEAN_TRUE);
		} else {
			fm.getProperty().set(LEGEND_AUTO_LAYOUT, TYPE_GRAPHICS, FeatureModelProperty.VALUE_BOOLEAN_FALSE);
			final Point legendPos = getLegend().getPos();
			fm.getProperty().set(LEGEND_POSITION, TYPE_GRAPHICS, legendPos.x + "," + legendPos.y);
		}
	}

	private void writeLayoutAlgorithm(final IFeatureModel fm) {
		fm.getProperty().set(LAYOUT_ALGORITHM, TYPE_GRAPHICS, Integer.toString(getLayout().getLayoutAlgorithm()));
		if (getLayout().hasVerticalLayout()) {
			fm.getProperty().set(LAYOUT, TYPE_GRAPHICS, VALUE_VERTICAL);
		} else {
			fm.getProperty().set(LAYOUT, TYPE_GRAPHICS, VALUE_HORIZONTAL);
		}
	}

}
