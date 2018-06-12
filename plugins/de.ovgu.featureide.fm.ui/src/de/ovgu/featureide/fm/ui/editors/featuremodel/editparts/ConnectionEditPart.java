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

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.GridLayout;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.Request;
import org.eclipse.gef.RequestConstants;
import org.eclipse.gef.commands.Command;
import org.eclipse.gef.editparts.AbstractConnectionEditPart;
import org.eclipse.gef.editpolicies.DirectEditPolicy;
import org.eclipse.gef.requests.DirectEditRequest;
import org.eclipse.gef.requests.SelectionRequest;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.core.editing.FeatureModelToNodeTraceModel.Origin;
import de.ovgu.featureide.fm.core.explanations.Reason;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelReason;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureConnection;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramExtension;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.CircleDecoration;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.CollapsedDecoration;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.ConnectionDecoration;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.ConnectionFigure;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.RelationDecoration;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.ChangeFeatureGroupTypeOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.MandatoryFeatureOperation;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * An editpart for connections between features and their parents. Creates the source decoration dependent on the mandatory property.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke
 */
public class ConnectionEditPart extends AbstractConnectionEditPart implements GUIDefaults {

	private static final DirectEditPolicy ROLE_DIRECT_EDIT_POLICY = new DirectEditPolicy() {

		@Override
		protected void showCurrentEditValue(DirectEditRequest request) {}

		@Override
		protected Command getDirectEditCommand(DirectEditRequest request) {
			return null;
		}
	};

	/** The currently active reason directed {@link Origin#CHILD_UP upward}. */
	private FeatureModelReason activeReasonUp;
	/** The currently active reason directed {@link Origin#CHILD_DOWN downward}. */
	private FeatureModelReason activeReasonDown;

	private Figure toolTipContent = new Figure();

	ConnectionEditPart(FeatureConnection connection) {
		setModel(connection);
	}

	@Override
	public FeatureConnection getModel() {
		return (FeatureConnection) super.getModel();
	}

	@Override
	public FeatureEditPart getSource() {
		return (FeatureEditPart) super.getSource();
	}

	@Override
	public FeatureEditPart getTarget() {
		return (FeatureEditPart) super.getTarget();
	}

	@Override
	public ConnectionFigure getFigure() {
		return (ConnectionFigure) super.getFigure();
	}

	@Override
	protected ConnectionFigure createFigure() {
		return new ConnectionFigure(connectsExternFeatures());
	}

	@Override
	protected void createEditPolicies() {
		if (connectsExternFeatures()) {
			return;
		}

		installEditPolicy(EditPolicy.DIRECT_EDIT_ROLE, ROLE_DIRECT_EDIT_POLICY);
	}

	@Override
	public void performRequest(Request request) {
		if (request.getType() == RequestConstants.REQ_OPEN) {
			final boolean success = changeMandatory(request);
			if (success) {
				return;
			}
			changeConnectionType();
		}
	}

	/**
	 * Change the mandatory type is the circle decoration was selected.
	 */
	private boolean changeMandatory(Request request) {
		final IFeature feature = getModel().getSource().getObject();
		if (feature.getStructure().getParent().isAnd()) {
			final List<?> decorators = getFigure().getChildren();
			if (!decorators.isEmpty()) {
				final Object child = decorators.get(0);
				if (child instanceof CircleDecoration) {
					final Rectangle decoratorBounds = new Rectangle(((CircleDecoration) child).getBounds());
					if (request instanceof SelectionRequest) {
						final Point requestLocation = ((SelectionRequest) request).getLocation();
						((CircleDecoration) child).translateToRelative(requestLocation);
						if (decoratorBounds.contains(requestLocation)) {
							final IFeatureModel featureModel = feature.getFeatureModel();
							final MandatoryFeatureOperation op = new MandatoryFeatureOperation(feature, featureModel);
							try {
								PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
							} catch (final ExecutionException e) {
								FMUIPlugin.getDefault().logError(e);
							}
							return true;
						}
					}
				}
			}
		}
		return false;
	}

	private void changeConnectionType() {
		if (connectsExternFeatures()) {
			return;
		}

		final IFeature feature = getModel().getTarget().getObject();
		final IFeatureModel featureModel = feature.getFeatureModel();

		int groupType;

		if (feature.getStructure().isAlternative()) {
			groupType = ChangeFeatureGroupTypeOperation.AND;
		} else if (feature.getStructure().isAnd()) {
			groupType = ChangeFeatureGroupTypeOperation.OR;
		} else {
			groupType = ChangeFeatureGroupTypeOperation.ALTERNATIVE;
		}

		final ChangeFeatureGroupTypeOperation op = new ChangeFeatureGroupTypeOperation(groupType, feature, featureModel);

		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
		} catch (final ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

	@Override
	protected void refreshVisuals() {
		refreshSourceDecoration();
		refreshParent();
		refreshTargetDecoration();
		refreshToolTip();
	}

	public void refreshParent() {
		final IGraphicalFeature newModel = getModel().getTarget();
		final FeatureEditPart newEditPart = (FeatureEditPart) getViewer().getEditPartRegistry().get(newModel);
		setTarget(newEditPart);
		getFigure().setVisible(getTarget() != null);

		if (activeReasonUp != null) {
			getFigure().setForegroundColor(FMPropertyManager.getReasonColor(activeReasonUp));
			getFigure().setLineWidth(FMPropertyManager.getReasonLineWidth(activeReasonUp));
		} else {
			getFigure().setForegroundColor(FMPropertyManager.getConnectionForegroundColor());
			getFigure().setLineWidth(1);
		}
		getFigure().revalidate();
	}

	public void refreshSourceDecoration() {
		final IFeature source = getModel().getSource().getObject();
		IFeature sourceParent = getModel().getSource().getObject();
		final IGraphicalFeature graphicalTarget = getModel().getTarget();
		final IGraphicalFeature graphicalSource = getModel().getSource();
		if ((graphicalTarget == null) || graphicalSource.hasCollapsedParent()) {
			return;
		}
		final IFeature target = graphicalTarget.getObject();

		boolean parentHidden = false;

		ConnectionDecoration sourceDecoration = null;
		while (!sourceParent.getStructure().isRoot()) {
			sourceParent = sourceParent.getStructure().getParent().getFeature();
			if (sourceParent.getStructure().isHidden()) {
				parentHidden = true;
			}

		}

		if (graphicalSource == graphicalTarget) {
			if (graphicalSource.isCollapsed()) {
				sourceDecoration = new CollapsedDecoration(graphicalTarget);
			}
		} else {
			if (target.getStructure().isAnd()
				&& (!source.getStructure().isHidden() || FeatureUIHelper.showHiddenFeatures(graphicalTarget.getGraphicalModel()))) {
				if (!(source.getStructure().isHidden() && !FeatureUIHelper.showHiddenFeatures(graphicalTarget.getGraphicalModel()))) {
					sourceDecoration = new CircleDecoration(source.getStructure().isMandatory());
				}
			}
		}

		getFigure().setSourceDecoration(sourceDecoration);
		if ((sourceDecoration != null) && (activeReasonDown != null)) {
			sourceDecoration.setActiveReason(activeReasonDown);
		}
	}

	public void refreshTargetDecoration() {
		// Check if there is a target to refresh.
		final IGraphicalFeature target = getModel().getTarget();
		if (target == null) {
			return;
		}

		/*
		 * Add a target decoration only if this is the main connection. The main connection is the first sibling and the only one with a target decoration.
		 */
		final IFeatureStructure targetStructure = target.getObject().getStructure();
		final IGraphicalFeature source = getModel().getSource();
		final IFeatureStructure sourceStructure = source.getObject().getStructure();
		final IFeatureStructure mainSourceStructure = targetStructure.getFirstChild();
		ConnectionDecoration targetDecoration = null;
		if ((sourceStructure == mainSourceStructure) && !targetStructure.isAnd() && (targetStructure.getChildrenCount() > 1)) {
			final List<IGraphicalFeature> graphicalChildren = FeatureUIHelper.getGraphicalChildren(target);
			if (!graphicalChildren.isEmpty()) { // Even if the target has children, it might be collapsed, leading to no graphical children.
				final IGraphicalFeature lastChild = FeatureUIHelper.hasVerticalLayout(target.getGraphicalModel()) ? graphicalChildren.get(0)
					: graphicalChildren.get(graphicalChildren.size() - 1);
				targetDecoration = new RelationDecoration(targetStructure.isMultiple(), lastChild);
			}
		}
		getFigure().setTargetDecoration(targetDecoration);

		/*
		 * Refresh the active reason of the target decoration of the main connection (which might not be this one). We have to do this whenever any connection
		 * is refreshed as the main connection might not be refreshed even though its target decoration has to be.
		 */
		final IGraphicalFeature mainSource = FeatureUIHelper.getGraphicalFeature(mainSourceStructure, target.getGraphicalModel());
		final ConnectionEditPart mainConnectionEditPart = (ConnectionEditPart) getViewer().getEditPartRegistry().get(mainSource.getSourceConnection());
		if (mainConnectionEditPart == null) {
			return;
		}
		final ConnectionDecoration mainTargetDecoration = mainConnectionEditPart.getFigure().getTargetDecoration();
		if (mainTargetDecoration == null) {
			return;
		}
		mainTargetDecoration.setActiveReason(getMainActiveReason());
	}

	public void refreshToolTip() {
		final IGraphicalFeature graphicalTarget = getModel().getTarget();
		if (graphicalTarget == null) {
			return;
		}
		final IFeature target = graphicalTarget.getObject();
		toolTipContent.removeAll();
		toolTipContent.setLayoutManager(new GridLayout());
		toolTipContent
				.add(new Label("Connection type:\n" + (target.getStructure().isAnd() ? "And" : (target.getStructure().isMultiple() ? "Or" : "Alternative"))));

		// Write the active reasons.
		final List<Reason<?>> activeReasons = new ArrayList<>(2);
		if (activeReasonUp != null) {
			activeReasons.add(activeReasonUp);
		}
		if (activeReasonDown != null) {
			activeReasons.add(activeReasonDown);
		}
		if (!activeReasons.isEmpty()) {
			String explanationString = "This connection is involved in the selected defect:";
			explanationString += activeReasons.get(0).getExplanation().getWriter().getReasonsString(activeReasons);
			toolTipContent.add(new Label(explanationString));
		}

		// call of the FeatureDiagramExtensions
		for (final FeatureDiagramExtension extension : FeatureDiagramExtension.getExtensions()) {
			toolTipContent = extension.extendConnectionToolTip(toolTipContent, this);
		}

		getFigure().setToolTip(toolTipContent);
	}

	@Override
	public void activate() {
		getFigure().setVisible(getTarget() != null);
		super.activate();
	}

	@Override
	public void deactivate() {
		super.deactivate();
		getFigure().setVisible(false);
	}

	/**
	 * Sets the active reason.
	 *
	 * @param activeReason the new active reason; null to reset
	 * @throws IllegalArgumentException if the reason's origin is not a vertical child relationship
	 */
	public void setActiveReason(FeatureModelReason activeReason) throws IllegalArgumentException {
		if (activeReason == null) {
			activeReasonUp = null;
			activeReasonDown = null;
			return;
		}
		switch (activeReason.getSubject().getOrigin()) {
		case CHILD_UP:
			activeReasonUp = activeReason;
			break;
		case CHILD_DOWN:
			activeReasonDown = activeReason;
			break;
		default:
			throw new IllegalArgumentException("Reason does not denote a vertical child relationship");
		}
	}

	/**
	 * Returns the active reason for use with the main connection's target decoration. The main active reason has the maximum confidence of all reasons of all
	 * siblings.
	 *
	 * @return the active reason for use with the main connection's target decoration
	 */
	private FeatureModelReason getMainActiveReason() {
		final IGraphicalFeature target = getModel().getTarget();
		if (target == null) {
			return null;
		}
		final IFeatureStructure targetStructure = target.getObject().getStructure();
		final IGraphicalFeature source = getModel().getSource();
		final IFeatureStructure sourceStructure = source.getObject().getStructure();
		FeatureModelReason mainActiveReason = null;
		for (final IFeatureStructure siblingStructure : targetStructure.getChildren()) {
			final IGraphicalFeature sibling;
			final ConnectionEditPart siblingConnectionEditPart;
			if (siblingStructure == sourceStructure) {
				// Don't bother looking up this edit part.
				sibling = source;
				siblingConnectionEditPart = this;
			} else {
				/*
				 * TODO Increase performance by accessing edit parts directly instead of looking them up. The sibling edit parts should be accessible through
				 * getTarget().getTargetConnections(). However, as of writing, that method always returns an empty list. As a result, the sibling edit parts
				 * have to be looked up with a detour to each sibling's model.
				 */
				sibling = FeatureUIHelper.getGraphicalFeature(siblingStructure, target.getGraphicalModel());
				siblingConnectionEditPart = (ConnectionEditPart) getViewer().getEditPartRegistry().get(sibling.getSourceConnection());
			}
			if (siblingConnectionEditPart == null) {
				continue;
			}
			final FeatureModelReason activeReason = siblingConnectionEditPart.activeReasonDown;
			if ((activeReason != null) && ((mainActiveReason == null) || (mainActiveReason.getConfidence() < activeReason.getConfidence()))) { // maximum
																																				 // confidence
																																				 // of all
																																				 // siblings
				mainActiveReason = activeReason;
			}
		}
		return mainActiveReason;
	}

	/**
	 * Checks if the target and source features are from an external feature model.
	 *
	 * @return true if both features are from an external feature model
	 */
	private boolean connectsExternFeatures() {
		final FeatureConnection featureConnection = getModel();
		final IFeature source = featureConnection.getSource().getObject();
		final IGraphicalFeature graphicalTarget = featureConnection.getTarget();
		if (graphicalTarget == null) {
			return false;
		}
		final IFeature target = graphicalTarget.getObject();
		return ((source instanceof ExtendedFeature) && ((ExtendedFeature) source).isFromExtern() && (target instanceof ExtendedFeature)
			&& ((ExtendedFeature) target).isFromExtern());
	}

	/*
	 * Catches the events thrown by the feature model editor and refreshes the connection accordingly. The events are forwarded by the FeatureEditPart.
	 */
	public void propertyChange(FeatureIDEEvent event) {
		final EventType prop = event.getEventType();
		if (EventType.PARENT_CHANGED.equals(prop)) {
			refreshParent();
		} else if (EventType.MANDATORY_CHANGED.equals(prop)) {
			refreshSourceDecoration();
		} else if (EventType.FEATURE_NAME_CHANGED.equals(prop)) {
			refreshVisuals();
		}
	}
}
