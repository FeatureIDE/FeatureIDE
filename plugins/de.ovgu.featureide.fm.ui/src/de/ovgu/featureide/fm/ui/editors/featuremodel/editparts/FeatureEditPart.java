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
package de.ovgu.featureide.fm.ui.editors.featuremodel.editparts;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.List;
import java.util.Map;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.IUndoContext;
import org.eclipse.draw2d.ConnectionAnchor;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.NodeEditPart;
import org.eclipse.gef.Request;
import org.eclipse.gef.RequestConstants;
import org.eclipse.gef.editparts.AbstractGraphicalEditPart;
import org.eclipse.gef.tools.DirectEditManager;
import org.eclipse.jface.viewers.TextCellEditor;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureConnection;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.commands.renaming.FeatureCellEditorLocator;
import de.ovgu.featureide.fm.ui.editors.featuremodel.commands.renaming.FeatureLabelEditManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.FeatureFigure;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureSetMandatoryOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.policies.FeatureDirectEditPolicy;

/**
 * An editpart for features. It implements the <code>NodeEditPart</code> that
 * the models of features can provide connection anchors.
 * 
 * @author Thomas Thuem
 */
public class FeatureEditPart extends AbstractGraphicalEditPart implements NodeEditPart, PropertyConstants, PropertyChangeListener {

	private ConnectionAnchor sourceAnchor = null;
	private ConnectionAnchor targetAnchor = null;

	FeatureEditPart(Object feature) {
		super();
		setModel(feature);
	}

	public Feature getFeature() {
		return (Feature) getModel();
	}

	public FeatureFigure getFeatureFigure() {
		return (FeatureFigure) getFigure();
	}

	@Override
	protected IFigure createFigure() {
		final Feature f = getFeature();
		final FeatureFigure featureFigure = new FeatureFigure(f, f.getFeatureModel());
		sourceAnchor = featureFigure.getSourceAnchor();
		targetAnchor = featureFigure.getTargetAnchor();
		return featureFigure;
	}

	@Override
	protected void createEditPolicies() {
		final Feature f = getFeature();
		installEditPolicy(EditPolicy.DIRECT_EDIT_ROLE, new FeatureDirectEditPolicy(f.getFeatureModel(), f));
	}

	private DirectEditManager manager;

	public void showRenameManager() {
		if (manager == null) {
			final Feature f = getFeature();
			manager = new FeatureLabelEditManager(this, TextCellEditor.class, new FeatureCellEditorLocator(getFeatureFigure()), f.getFeatureModel());
		}
		manager.show();
	}

	@Override
	public void performRequest(Request request) {
		Feature feature = getFeature();
		FeatureModel featureModel = ((ModelEditPart) this.getParent()).getFeatureModel();

		for (Constraint constraint : featureModel.getConstraints()) {
			if (constraint.isFeatureSelected())
				constraint.setFeatureSelected(false);
		}

		if (request.getType() == RequestConstants.REQ_DIRECT_EDIT) {
			showRenameManager();
		} else if (request.getType() == RequestConstants.REQ_OPEN) {
			if (feature.isRoot() || !feature.getParent().isAnd()) {
				return;
			}

			FeatureSetMandatoryOperation op = new FeatureSetMandatoryOperation(feature, featureModel);
			op.addContext((IUndoContext) featureModel.getUndoContext());
			try {
				PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
			} catch (ExecutionException e) {
				FMUIPlugin.getDefault().logError(e);

			}

			featureModel.handleModelDataChanged();
		} else if (request.getType() == RequestConstants.REQ_SELECTION) {
			for (Constraint partOf : feature.getRelevantConstraints()) {
				partOf.setFeatureSelected(true);
			}
		}
	}

	@Override
	protected List<FeatureConnection> getModelSourceConnections() {
		return ((Feature) getModel()).getSourceConnections();
	}

	@Override
	protected List<FeatureConnection> getModelTargetConnections() {
		return ((Feature) getModel()).getTargetConnections();
	}

	public ConnectionAnchor getSourceConnectionAnchor(org.eclipse.gef.ConnectionEditPart connection) {
		return sourceAnchor;
	}

	public ConnectionAnchor getSourceConnectionAnchor(Request request) {
		return sourceAnchor;
	}

	public ConnectionAnchor getTargetConnectionAnchor(org.eclipse.gef.ConnectionEditPart connection) {
		return targetAnchor;
	}

	public ConnectionAnchor getTargetConnectionAnchor(Request request) {
		return targetAnchor;
	}

	@Override
	public void activate() {
		getFeature().addListener(this);
		super.activate();
	}

	@Override
	public void deactivate() {
		super.deactivate();
		getFeature().removeListener(this);
	}

	public void propertyChange(PropertyChangeEvent event) {
		String prop = event.getPropertyName();
		if (LOCATION_CHANGED.equals(prop)) {
			getFeatureFigure().setLocation((Point) event.getNewValue());
			for (FeatureConnection connection : getFeature().getTargetConnections()) {
				Map<?, ?> registry = getViewer().getEditPartRegistry();
				ConnectionEditPart connectionEditPart = (ConnectionEditPart) registry.get(connection);
				if (connectionEditPart != null) {
					connectionEditPart.refreshSourceDecoration();
					connectionEditPart.refreshTargetDecoration();
					connectionEditPart.refreshToolTip();
				}
			}
		} else if (CHILDREN_CHANGED.equals(prop)) {
			getFeatureFigure().setProperties();
			for (FeatureConnection connection : getFeature().getTargetConnections()) {
				Map<?, ?> registry = getViewer().getEditPartRegistry();
				ConnectionEditPart connectionEditPart = (ConnectionEditPart) registry.get(connection);
				if (connectionEditPart != null) {
					connectionEditPart.refreshSourceDecoration();
					connectionEditPart.refreshTargetDecoration();
					connectionEditPart.refreshToolTip();
				}
			}
		} else if (NAME_CHANGED.equals(prop)) {
			getFeatureFigure().setName(getFeature().getDisplayName());
			FeatureUIHelper.setSize(getFeature(), getFeatureFigure().getSize());
		} else if (ATTRIBUTE_CHANGED.equals(prop)) {
			getFeatureFigure().setProperties();
		}
	}

}
