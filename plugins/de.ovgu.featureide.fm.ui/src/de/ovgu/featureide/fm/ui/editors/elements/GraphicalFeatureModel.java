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

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.IPropertyContainer;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.impl.Constraint;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
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

	protected final IFeatureModelManager featureModelManager;

	protected final FeatureModelLayout layout;

	protected Map<IFeature, IGraphicalFeature> features = new HashMap<IFeature, IGraphicalFeature>();
	protected Map<IConstraint, IGraphicalConstraint> constraints = new HashMap<IConstraint, IGraphicalConstraint>();

	protected boolean hiddenLegend = false;
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
		final IFeatureModel featureModel = featureModelManager.editObject();
		final ArrayList<IGraphicalFeature> featureList = new ArrayList<>(featureModel.getNumberOfFeatures());
		for (final IFeature f : featureModel.getVisibleFeatures(getLayout().showHiddenFeatures())) {
			featureList.add(getGraphicalFeature(f));
		}
		return Collections.unmodifiableCollection(featureList);
	}

	@Override
	public Collection<IGraphicalFeature> getAllFeatures() {
		final IFeatureModel featureModel = featureModelManager.editObject();
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
		final IFeatureModel featureModel = featureModelManager.editObject();
		final ArrayList<IGraphicalConstraint> constraintList = new ArrayList<>(featureModel.getConstraintCount());
		for (final IConstraint c : featureModel.getConstraints()) {
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
		final IFeatureModel featureModel = featureModelManager.editObject();
		final IFeatureStructure root = featureModel.getStructure().getRoot();
		if (root != null) {
			constraints = new HashMap<>((int) (featureModel.getConstraintCount() * 1.5));
			for (final IConstraint constraint : featureModel.getConstraints()) {
				constraints.put(constraint, new GraphicalConstraint(constraint, this));
			}

			features = new HashMap<>((int) (featureModel.getNumberOfFeatures() * 1.5));
			for (final IFeature feature : featureModel.getVisibleFeatures(getLayout().showHiddenFeatures())) {
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
			final IGraphicalConstraint gTemp = getGraphicalConstraint(featureModelManager.editObject().getConstraints().get(i));
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
		// TODO Auto-generated method stub
		return currentlyActiveExplanation;
	}

	private static final String CHOSEN_LAYOUT_ALGORITHM = "chosenLayoutAlgorithm";
	private static final String TRUE = "true";
	private static final String FALSE = "false";
	private static final String SHOW_HIDDEN_FEATURES = "showHiddenFeatures";
	private static final String SHOW_COLLAPSED_CONSTRAINTS = "showCollapsedConstraints";
	private static final String LEGEND_AUTO_LAYOUT = "autoLayout";
	private static final String LEGEND_HIDDEN = "hidden";
	private static final String SHOW_SHORT_NAMES = "showShortNames";
	private static final String TYPE_GRAPHICS = "graphics";
	private static final String LAYOUT = "layout";

	@Override
	public void readValues() {
		final IFeatureModel fm = featureModelManager.editObject();

		getLayout().setLayout(Integer.parseInt(fm.getProperty().get(CHOSEN_LAYOUT_ALGORITHM, TYPE_GRAPHICS, "1")));

		switch (fm.getProperty().get(LAYOUT, TYPE_GRAPHICS, "horizontal")) {
		case "vertical":
			getLayout().setVerticalLayout(true);
		case "horizontal":
		default:
			getLayout().setVerticalLayout(false);
		}

		final Boolean hiddenFeatures = getBooleanProperty(fm.getProperty(), SHOW_HIDDEN_FEATURES);
		getLayout().showHiddenFeatures(hiddenFeatures != null ? hiddenFeatures : true);

		final Boolean shortNames = getBooleanProperty(fm.getProperty(), SHOW_SHORT_NAMES);
		getLayout().setShowShortNames(shortNames != null ? shortNames : false);

		final Boolean colapsedConstraints = getBooleanProperty(fm.getProperty(), SHOW_COLLAPSED_CONSTRAINTS);
		getLayout().showCollapsedConstraints(colapsedConstraints != null ? colapsedConstraints : true);

		final Boolean legendHidden = getBooleanProperty(fm.getProperty(), LEGEND_HIDDEN);
		setLegendHidden(legendHidden != null ? legendHidden : false);

		final Boolean legendAutoLayout = getBooleanProperty(fm.getProperty(), LEGEND_AUTO_LAYOUT);
		getLayout().setLegendAutoLayout(legendAutoLayout != null ? legendAutoLayout : true);

		if (!getLayout().hasLegendAutoLayout()) {
			final Point legendPos = new Point();
			legendPos.x = Integer.parseInt(fm.getProperty().get("legendx", TYPE_GRAPHICS, "0"));
			legendPos.y = Integer.parseInt(fm.getProperty().get("legendy", TYPE_GRAPHICS, "0"));
			getLegend().setPos(legendPos);
		}

		final boolean manualLayout = !getLayout().hasFeaturesAutoLayout();
		for (final IGraphicalFeature graphicalFeature : getAllFeatures()) {
			final IPropertyContainer customProperties = fm.getFeature(graphicalFeature.getObject().getName()).getCustomProperties();
			if (manualLayout) {
				final Point location = new Point();
				location.x = Integer.parseInt(customProperties.get("positionx", TYPE_GRAPHICS, "0"));
				location.y = Integer.parseInt(customProperties.get("positiony", TYPE_GRAPHICS, "0"));
				graphicalFeature.setLocation(location);
			}

			final Boolean isCollapsed = getBooleanProperty(customProperties, "collapsed");
			graphicalFeature.setCollapsed(isCollapsed != null ? isCollapsed : false);
		}
		for (final IGraphicalConstraint constr : getConstraints()) {
			final IPropertyContainer customProperties = constr.getObject().getCustomProperties();
			if (manualLayout) {
				final Point location = new Point();
				location.x = Integer.parseInt(customProperties.get("positionx", TYPE_GRAPHICS, "0"));
				location.y = Integer.parseInt(customProperties.get("positiony", TYPE_GRAPHICS, "0"));
				constr.setLocation(location);
			}
		}
	}

	private Boolean getBooleanProperty(IPropertyContainer properties, String name) {
		final String value;
		try {
			value = properties.get(name, TYPE_GRAPHICS);
		} catch (final IPropertyContainer.NoSuchPropertyException e) {
			return null;
		}
		switch (value) {
		case FALSE:
			return false;
		case TRUE:
			return true;
		default:
			return null;
		}
	}

	@Override
	public void writeValues() {
		final IFeatureModel fm = featureModelManager.editObject();
		writeLayoutAlgorithm(fm);
		writeAttributes(fm);
		writeLegend(fm);
		for (final IGraphicalFeature graphicalFeature : getAllFeatures()) {
			writeFeature(fm, graphicalFeature);
		}
		for (final IGraphicalConstraint graphicalConstraint : getConstraints()) {
			writeConstraint(graphicalConstraint);
		}
	}

	private void writeConstraint(final IGraphicalConstraint graphicalConstraint) {
		final IPropertyContainer customProperties = graphicalConstraint.getObject().getCustomProperties();
		final Point location = graphicalConstraint.getLocation();
		if (!getLayout().hasFeaturesAutoLayout()) {
			customProperties.set("positionx", TYPE_GRAPHICS, Integer.toString(location.x));
			customProperties.set("positiony", TYPE_GRAPHICS, Integer.toString(location.y));
		} else {
			customProperties.remove("positionx", TYPE_GRAPHICS);
			customProperties.remove("positiony", TYPE_GRAPHICS);
		}
	}

	private void writeFeature(final IFeatureModel fm, final IGraphicalFeature graphicalFeature) {
		final IPropertyContainer customProperties = fm.getFeature(graphicalFeature.getObject().getName()).getCustomProperties();
		if (!getLayout().hasFeaturesAutoLayout()) {
			final Point location = graphicalFeature.getLocation();
			customProperties.set("positionx", TYPE_GRAPHICS, Integer.toString(location.x));
			customProperties.set("positiony", TYPE_GRAPHICS, Integer.toString(location.y));
		} else {
			customProperties.remove("positionx", TYPE_GRAPHICS);
			customProperties.remove("positiony", TYPE_GRAPHICS);
		}
		if (graphicalFeature.isCollapsed()) {
			customProperties.set("collapsed", TYPE_GRAPHICS, TRUE);
		} else if (customProperties.has("collapsed", TYPE_GRAPHICS)) {
			customProperties.set("collapsed", TYPE_GRAPHICS, FALSE);
		}
	}

	private void writeAttributes(final IFeatureModel fm) {
		if (getLayout().showHiddenFeatures()) {
			fm.getProperty().set(SHOW_HIDDEN_FEATURES, TYPE_GRAPHICS, TRUE);
		} else {
			fm.getProperty().set(SHOW_HIDDEN_FEATURES, TYPE_GRAPHICS, FALSE);
		}
		if (getLayout().showShortNames()) {
			fm.getProperty().set(SHOW_SHORT_NAMES, TYPE_GRAPHICS, TRUE);
		} else {
			fm.getProperty().set(SHOW_SHORT_NAMES, TYPE_GRAPHICS, FALSE);
		}
		if (getLayout().showCollapsedConstraints()) {
			fm.getProperty().set(SHOW_COLLAPSED_CONSTRAINTS, TYPE_GRAPHICS, TRUE);
		} else {
			fm.getProperty().set(SHOW_COLLAPSED_CONSTRAINTS, TYPE_GRAPHICS, FALSE);
		}
	}

	private void writeLegend(final IFeatureModel fm) {
		if (isLegendHidden()) {
			fm.getProperty().set(LEGEND_HIDDEN, TYPE_GRAPHICS, TRUE);
		} else {
			fm.getProperty().set(LEGEND_HIDDEN, TYPE_GRAPHICS, FALSE);
		}
		if (getLayout().hasLegendAutoLayout()) {
			fm.getProperty().set(LEGEND_AUTO_LAYOUT, TYPE_GRAPHICS, TRUE);
		} else {
			fm.getProperty().set(LEGEND_AUTO_LAYOUT, TYPE_GRAPHICS, FALSE);
			final Point legendPos = getLegend().getPos();
			fm.getProperty().set("legendx", TYPE_GRAPHICS, Integer.toString(legendPos.x));
			fm.getProperty().set("legendy", TYPE_GRAPHICS, Integer.toString(legendPos.y));
		}
	}

	private void writeLayoutAlgorithm(final IFeatureModel fm) {
		fm.getProperty().set(CHOSEN_LAYOUT_ALGORITHM, TYPE_GRAPHICS, Integer.toString(getLayout().getLayoutAlgorithm()));
		if (getLayout().hasVerticalLayout()) {
			fm.getProperty().set(LAYOUT, TYPE_GRAPHICS, "vertical");
		} else {
			fm.getProperty().set(LAYOUT, TYPE_GRAPHICS, "horizontal");
		}
	}

}
