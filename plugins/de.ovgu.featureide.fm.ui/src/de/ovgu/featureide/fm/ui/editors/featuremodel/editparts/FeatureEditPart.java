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
package de.ovgu.featureide.fm.ui.editors.featuremodel.editparts;

import static de.ovgu.featureide.fm.core.localization.StringTable.COLLAPSE_OPERATION;

import java.util.Collections;
import java.util.List;
import java.util.Map;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.draw2d.ConnectionAnchor;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.NodeEditPart;
import org.eclipse.gef.Request;
import org.eclipse.gef.RequestConstants;
import org.eclipse.gef.tools.DirectEditManager;
import org.eclipse.jface.viewers.TextCellEditor;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.editing.FeatureModelToNodeTraceModel.Origin;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelReason;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureConnection;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.commands.renaming.FeatureCellEditorLocator;
import de.ovgu.featureide.fm.ui.editors.featuremodel.commands.renaming.FeatureLabelEditManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.FeatureFigure;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.CollapseFeatureOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.policies.FeatureDirectEditPolicy;

/**
 * An editpart for features. It implements the <code>NodeEditPart</code> that the models of features can provide connection anchors.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke
 */
public class FeatureEditPart extends ModelElementEditPart implements NodeEditPart {

	private ConnectionAnchor sourceAnchor = null;
	private ConnectionAnchor targetAnchor = null;

	FeatureEditPart(IGraphicalFeature feature) {
		setModel(feature);
	}

	@Override
	public ModelEditPart getParent() {
		return super.getParent();
	}

	@Override
	public IGraphicalFeature getModel() {
		return (IGraphicalFeature) super.getModel();
	}

	@Override
	public FeatureFigure getFigure() {
		return (FeatureFigure) super.getFigure();
	}

	@Override
	protected FeatureFigure createFigure() {
		final IGraphicalFeature f = getModel();
		final FeatureFigure featureFigure = new FeatureFigure(f, f.getGraphicalModel());
		sourceAnchor = featureFigure.getSourceAnchor();
		targetAnchor = featureFigure.getTargetAnchor();
		return featureFigure;
	}

	@Override
	protected void createEditPolicies() {
		final IGraphicalFeature f = getModel();
		installEditPolicy(EditPolicy.DIRECT_EDIT_ROLE, new FeatureDirectEditPolicy(f.getGraphicalModel(), f));
	}

	private DirectEditManager manager;

	public void showRenameManager() {
		if (manager == null) {
			final IGraphicalFeature f = getModel();
			manager =
				new FeatureLabelEditManager(this, TextCellEditor.class, new FeatureCellEditorLocator(getFigure()), f.getGraphicalModel().getFeatureModel());
		}
		manager.show();
	}

	@Override
	public void performRequest(Request request) {
		final IFeature feature = getModel().getObject();
		final IGraphicalFeatureModel featureModel = getParent().getModel();

		for (final IGraphicalConstraint constraint : featureModel.getConstraints()) {
			if (constraint.isFeatureSelected()) {
				constraint.setFeatureSelected(false);
			}
		}

		if (request.getType() == RequestConstants.REQ_DIRECT_EDIT) {
			showRenameManager();
		} else if (request.getType() == RequestConstants.REQ_OPEN) {
			final CollapseFeatureOperation op = new CollapseFeatureOperation(feature, featureModel, COLLAPSE_OPERATION);
			try {
				PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
			} catch (final ExecutionException e) {
				FMUIPlugin.getDefault().logError(e);

			}
		} else if (request.getType() == RequestConstants.REQ_SELECTION) {
			for (final IConstraint partOf : feature.getStructure().getRelevantConstraints()) {
				featureModel.getGraphicalConstraint(partOf).setFeatureSelected(true);
			}
		}
	}

	/**
	 * Returns the source connection.
	 *
	 * @return the source connection; null if none exists
	 */
	protected ConnectionEditPart getSourceConnection() {
		if (getSourceConnections().isEmpty()) {
			return null;
		}
		return (ConnectionEditPart) getSourceConnections().get(0);
	}

	@Override
	protected List<FeatureConnection> getModelSourceConnections() {
		return getModel().getSourceConnectionAsList();
	}

	@Override
	protected List<FeatureConnection> getModelTargetConnections() {
		return Collections.<FeatureConnection> emptyList();// getModel().getTargetConnections();
	}

	@Override
	public ConnectionAnchor getSourceConnectionAnchor(org.eclipse.gef.ConnectionEditPart connection) {
		if (getModel().isCollapsed() && (connection.getTarget() == connection.getSource())) {
			return targetAnchor;
		}
		return sourceAnchor;
	}

	@Override
	public ConnectionAnchor getSourceConnectionAnchor(Request request) {
		return sourceAnchor;
	}

	@Override
	public ConnectionAnchor getTargetConnectionAnchor(org.eclipse.gef.ConnectionEditPart connection) {
		return targetAnchor;
	}

	@Override
	public ConnectionAnchor getTargetConnectionAnchor(Request request) {
		return targetAnchor;
	}

	@Override
	public void activate() {
		getModel().registerUIObject(this);
		super.activate();
	}

	@Override
	public void deactivate() {
		super.deactivate();
	}

	@Override
	public void refresh() {
		super.refresh();
	}

	@Override
	public void propertyChange(FeatureIDEEvent event) {
		final EventType prop = event.getEventType();
		FeatureConnection sourceConnection;
		switch (prop) {
		case CHILDREN_CHANGED:
			getFigure().setLocation(getModel().getLocation());
			for (final FeatureConnection connection : getModel().getTargetConnections()) {
				final Map<?, ?> registry = getViewer().getEditPartRegistry();
				final ConnectionEditPart connectionEditPart = (ConnectionEditPart) registry.get(connection);
				if (connectionEditPart != null) {
					connectionEditPart.refresh();
				}
			}
			break;
		case LOCATION_CHANGED:
			getFigure().setLocation(getModel().getLocation());
			getFigure().setProperties();
			sourceConnection = getModel().getSourceConnection();
			if (sourceConnection != null) {
				final IGraphicalFeature target = sourceConnection.getTarget();
				final IGraphicalFeature newTarget = FeatureUIHelper.getGraphicalParent(getModel());
				if (!equals(newTarget, target)) {
					sourceConnection.setTarget(newTarget);
					final Map<?, ?> registry = getViewer().getEditPartRegistry();
					final ConnectionEditPart connectionEditPart = (ConnectionEditPart) registry.get(sourceConnection);
					if (connectionEditPart != null) {
						refresh();
					}
				}
			}

			for (final FeatureConnection connection : getModel().getTargetConnections()) {
				final Map<?, ?> registry = getViewer().getEditPartRegistry();
				final ConnectionEditPart connectionEditPart = (ConnectionEditPart) registry.get(connection);
				if (connectionEditPart != null) {
					connectionEditPart.refresh();
				}
			}
			break;
		case GROUP_TYPE_CHANGED:
			getFigure().setProperties();
			sourceConnection = getModel().getSourceConnection();
			Map<?, ?> registry = getViewer().getEditPartRegistry();
			ConnectionEditPart connectionEditPart = (ConnectionEditPart) registry.get(sourceConnection);
			if (connectionEditPart != null) {
				connectionEditPart.refreshSourceDecoration();
				connectionEditPart.refreshTargetDecoration();
				connectionEditPart.refreshToolTip();
			}
			break;
		case FEATURE_NAME_CHANGED:
			String displayName = getModel().getObject().getName();

			if (getModel().getGraphicalModel().getLayout().showShortNames()) {
				int lastIndexOf = displayName.lastIndexOf(".");
				displayName = displayName.substring(++lastIndexOf);
			}
			getFigure().setName(displayName);
			getModel().setSize(getFigure().getSize());

			sourceConnection = getModel().getSourceConnection();
			registry = getViewer().getEditPartRegistry();
			connectionEditPart = (ConnectionEditPart) registry.get(sourceConnection);
			connectionEditPart.propertyChange(event);
			break;
		case COLOR_CHANGED:
		case ATTRIBUTE_CHANGED:
			getFigure().setProperties();
			getModel().setSize(getFigure().getSize());
			break;
		case COLLAPSED_ALL_CHANGED:
		case COLLAPSED_CHANGED:
			/*
			 * Reset the active reason in case we missed that it was set to null while this was collapsed. In case it should not be null, the active reason will
			 * be set to the correct value in the upcoming feature model analysis anyway.
			 */
			setActiveReason(null); // reset includes a refresh (getFigure().setProperties())
			break;
		case MANDATORY_CHANGED:
			sourceConnection = getModel().getSourceConnection();
			registry = getViewer().getEditPartRegistry();
			connectionEditPart = (ConnectionEditPart) registry.get(sourceConnection);
			connectionEditPart.refreshSourceDecoration();
			connectionEditPart.propertyChange(event);
			break;
		case FEATURE_DELETE:
			deactivate();
			break;
		case PARENT_CHANGED:
			sourceConnection = getModel().getSourceConnection();
			registry = getViewer().getEditPartRegistry();
			connectionEditPart = (ConnectionEditPart) registry.get(sourceConnection);
			connectionEditPart.refreshVisuals();
			connectionEditPart.propertyChange(event);
			break;
		case HIDDEN_CHANGED:
			getFigure().setProperties();
			sourceConnection = getModel().getSourceConnection();
			registry = getViewer().getEditPartRegistry();
			connectionEditPart = (ConnectionEditPart) registry.get(sourceConnection);
			connectionEditPart.refreshSourceDecoration();
			break;
		case ACTIVE_EXPLANATION_CHANGED:
			setActiveReason(null); // reset
			break;
		case ACTIVE_REASON_CHANGED:
			setActiveReason((FeatureModelReason) event.getNewValue());
			break;
		default:
			FMUIPlugin.getDefault().logWarning(prop + " @ " + getModel() + " not handled.");
			break;
		}
	}

	/**
	 * <p> Sets the currently active reason. </p>
	 *
	 * <p> Propagates into the figure and the source connection. Refreshes accordingly. </p>
	 *
	 * @param activeReason the new active reason; null to reset
	 */
	protected void setActiveReason(FeatureModelReason activeReason) {
		// Update the figure.
		if ((activeReason == null // reset
		) || (activeReason.getSubject().getOrigin() == Origin.CHILD_HORIZONTAL)) {
			final FeatureFigure figure = getFigure();
			figure.setActiveReason(activeReason);
			figure.setProperties();
		}

		// Update the source connection.
		if ((activeReason == null // reset
		) || (activeReason.getSubject().getOrigin() == Origin.CHILD_UP) || (activeReason.getSubject().getOrigin() == Origin.CHILD_DOWN)) {
			final ConnectionEditPart sourceConnection = getSourceConnection();
			sourceConnection.setActiveReason(activeReason);
			sourceConnection.refreshVisuals();
		}
	}

	private static boolean equals(final IGraphicalFeature newTarget, final IGraphicalFeature target) {
		return newTarget == null ? target == null : newTarget.equals(target);
	}

}
