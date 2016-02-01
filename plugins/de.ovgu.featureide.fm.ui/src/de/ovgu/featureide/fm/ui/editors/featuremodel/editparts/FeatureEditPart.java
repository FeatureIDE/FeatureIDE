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

import java.util.List;
import java.util.Map;

import org.eclipse.core.commands.ExecutionException;
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

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureConnection;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.commands.renaming.FeatureCellEditorLocator;
import de.ovgu.featureide.fm.ui.editors.featuremodel.commands.renaming.FeatureLabelEditManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.FeatureFigure;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.SetFeatureToMandatoryOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.policies.FeatureDirectEditPolicy;

/**
 * An editpart for features. It implements the <code>NodeEditPart</code> that
 * the models of features can provide connection anchors.
 * 
 * @author Thomas Thuem
 * @author Marcus Pinnecke
 */
public class FeatureEditPart extends AbstractGraphicalEditPart implements NodeEditPart, IEventListener {

	private ConnectionAnchor sourceAnchor = null;
	private ConnectionAnchor targetAnchor = null;

	FeatureEditPart(Object feature) {
		super();
		setModel(feature);
	}

	public IGraphicalFeature getFeature() {
		return (IGraphicalFeature) getModel();
	}

	public FeatureFigure getFeatureFigure() {
		return (FeatureFigure) getFigure();
	}

	@Override
	protected IFigure createFigure() {
		final IGraphicalFeature f = getFeature();
		final FeatureFigure featureFigure = new FeatureFigure(f, f.getGraphicalModel());
		sourceAnchor = featureFigure.getSourceAnchor();
		targetAnchor = featureFigure.getTargetAnchor();
		return featureFigure;
	}

	@Override
	protected void createEditPolicies() {
		final IGraphicalFeature f = getFeature();
		installEditPolicy(EditPolicy.DIRECT_EDIT_ROLE, new FeatureDirectEditPolicy(f.getGraphicalModel(), f));
	}

	private DirectEditManager manager;

	public void showRenameManager() {
		if (manager == null) {
			final IGraphicalFeature f = getFeature();
			manager = new FeatureLabelEditManager(this, TextCellEditor.class, new FeatureCellEditorLocator(getFeatureFigure()), f.getGraphicalModel().getFeatureModel());
		}
		manager.show();
	}

	@Override
	public void performRequest(Request request) {
		IFeature feature = getFeature().getObject();
		IGraphicalFeatureModel featureModel = ((ModelEditPart) this.getParent()).getFeatureModel();

		for (IGraphicalConstraint constraint : featureModel.getConstraints()) {
			if (constraint.isFeatureSelected())
				constraint.setFeatureSelected(false);
		}

		if (request.getType() == RequestConstants.REQ_DIRECT_EDIT) {
			showRenameManager();
		} else if (request.getType() == RequestConstants.REQ_OPEN) {
			if (feature.getStructure().isRoot() || !feature.getStructure().getParent().isAnd()) {
				return;
			}

			SetFeatureToMandatoryOperation op = new SetFeatureToMandatoryOperation(feature, featureModel.getFeatureModel());
//TODO _interfaces Removed Code
			try {
				PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
			} catch (ExecutionException e) {
				FMUIPlugin.getDefault().logError(e);

			}
		} else if (request.getType() == RequestConstants.REQ_SELECTION) {
			for (IConstraint partOf : feature.getStructure().getRelevantConstraints()) {
				partOf.setFeatureSelected(true);
			}
		}
	}

	@Override
	protected List<FeatureConnection> getModelSourceConnections() {
		return getFeature().getSourceConnections();
	}

	@Override
	protected List<FeatureConnection> getModelTargetConnections() {
		return getFeature().getTargetConnections();
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
		getFeature().getObject().addListener(this);
		super.activate();
	}

	@Override
	public void deactivate() {
		super.deactivate();
		getFeature().getObject().removeListener(this);
	}

	public void propertyChange(FeatureIDEEvent event) {
		EventType prop = event.getEventType();
		if (EventType.LOCATION_CHANGED.equals(prop)) {
			if (!event.getOldValue().equals(event.getNewValue())) {
				getFeatureFigure().setLocation((Point) event.getNewValue());
			}
			for (FeatureConnection connection : getFeature().getTargetConnections()) {
				Map<?, ?> registry = getViewer().getEditPartRegistry();
				ConnectionEditPart connectionEditPart = (ConnectionEditPart) registry.get(connection);
				if (connectionEditPart != null) {
					connectionEditPart.refreshSourceDecoration();
					connectionEditPart.refreshTargetDecoration();
				}
			}
		} else if (EventType.CHILDREN_CHANGED.equals(prop)) {
			getFeatureFigure().setProperties();
			boolean targetUpdated = false;
			for (FeatureConnection connection : getFeature().getTargetConnections()) {
				Map<?, ?> registry = getViewer().getEditPartRegistry();
				ConnectionEditPart connectionEditPart = (ConnectionEditPart) registry.get(connection);
				if (connectionEditPart != null) {
					connectionEditPart.refreshSourceDecoration();
					if (!targetUpdated) {
						connectionEditPart.refreshTargetDecoration();
						connectionEditPart.refreshToolTip();
						targetUpdated = true;
					}
				}
			}
		} else if (EventType.NAME_CHANGED.equals(prop)) {
			getFeatureFigure().setName(getFeature().getObject().getProperty().getDisplayName());
			FeatureUIHelper.setSize(getFeature(), getFeatureFigure().getSize());
		} else if (EventType.ATTRIBUTE_CHANGED.equals(prop)) {
			getFeatureFigure().setProperties();
		} else if (EventType.MANDATORY_CHANGED.equals(prop)) {
			for (FeatureConnection connection : getFeature().getSourceConnections()) {
				Map<?, ?> registry = getViewer().getEditPartRegistry();
				ConnectionEditPart connectionEditPart = (ConnectionEditPart) registry.get(connection);
				connectionEditPart.refreshSourceDecoration();}
		}
	}

}
