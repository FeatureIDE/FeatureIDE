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

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.GridLayout;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.PolylineConnection;
import org.eclipse.draw2d.RotatableDecoration;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.Request;
import org.eclipse.gef.RequestConstants;
import org.eclipse.gef.commands.Command;
import org.eclipse.gef.editparts.AbstractConnectionEditPart;
import org.eclipse.gef.editpolicies.DirectEditPolicy;
import org.eclipse.gef.requests.DirectEditRequest;
import org.eclipse.swt.SWT;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.PropertyConstants;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureConnection;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramExtension;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.CircleDecoration;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.RelationDecoration;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.ChangeFeatureGroupTypeOperation;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * An editpart for connections between features and their parents. Creates the
 * source decoration dependent on the mandatory property.
 * 
 * @author Thomas Thuem
 * @author Marcus Pinnecke
 */
public class ConnectionEditPart extends AbstractConnectionEditPart implements GUIDefaults, PropertyConstants, PropertyChangeListener {

	private static final DirectEditPolicy ROLE_DIRECT_EDIT_POLICY = new DirectEditPolicy() {
		@Override
		protected void showCurrentEditValue(DirectEditRequest request) {
		}

		@Override
		protected Command getDirectEditCommand(DirectEditRequest request) {
			return null;
		}
	};

	private Figure toolTipContent = new Figure();

	ConnectionEditPart(Object connection) {
		super();
		setModel(connection);
	}

	public FeatureConnection getConnectionModel() {
		return (FeatureConnection) getModel();
	}

	@Override
	protected IFigure createFigure() {
		PolylineConnection figure = new PolylineConnection();
		figure.setForegroundColor(FMPropertyManager.getConnectionForgroundColor());

		FeatureConnection featureConnection = getConnectionModel();
		if (featureConnection.getSource() instanceof ExtendedFeature && ((ExtendedFeature) featureConnection.getSource()).isFromExtern()
				&& featureConnection.getTarget() instanceof ExtendedFeature && ((ExtendedFeature) featureConnection.getTarget()).isFromExtern()) {
			figure.setLineStyle(SWT.LINE_DASH);
		}

		return figure;
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
			changeConnectionType();
		}
	}

	private void changeConnectionType() {
		if (connectsExternFeatures()) {
			return;
		}

		IFeature feature = getConnectionModel().getTarget().getObject();
		IFeatureModel featureModel = feature.getFeatureModel();

		int groupType;

		if (feature.getStructure().isAlternative()) {
			groupType = ChangeFeatureGroupTypeOperation.AND;
		} else if (feature.getStructure().isAnd()) {
			groupType = ChangeFeatureGroupTypeOperation.OR;
		} else {
			groupType = ChangeFeatureGroupTypeOperation.ALTERNATIVE;
		}

		ChangeFeatureGroupTypeOperation op = new ChangeFeatureGroupTypeOperation(groupType, feature, featureModel);

		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
		} catch (ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);
		}

		featureModel.handleModelDataChanged();
	}

	@Override
	protected void refreshVisuals() {
		refreshParent();
		refreshSourceDecoration();
		refreshTargetDecoration();
		refreshToolTip();
	}

	public void refreshParent() {
		IGraphicalFeature newModel = getConnectionModel().getTarget();
		FeatureEditPart newEditPart = (FeatureEditPart) getViewer().getEditPartRegistry().get(newModel);
		setTarget(newEditPart);
	}

	public void refreshSourceDecoration() {
		IFeature source = getConnectionModel().getSource().getObject();
		IFeature sourceParent = getConnectionModel().getSource().getObject();
		IFeature target = getConnectionModel().getTarget().getObject();

		boolean parentHidden = false;

		RotatableDecoration sourceDecoration = null;
		while (!sourceParent.getStructure().isRoot()) {
			sourceParent = sourceParent.getStructure().getParent().getFeature();
			if (sourceParent.getStructure().isHidden())
				parentHidden = true;

		}
		if ((target.getStructure().isAnd()) && !(source.getStructure().isHidden() && !FeatureUIHelper.showHiddenFeatures(getConnectionModel().getTarget().getGraphicalModel())))
			if (!(parentHidden && !FeatureUIHelper.showHiddenFeatures(getConnectionModel().getTarget().getGraphicalModel())))
				sourceDecoration = new CircleDecoration(source.getStructure().isMandatory());

		PolylineConnection connection = (PolylineConnection) getConnectionFigure();
		connection.setSourceDecoration(sourceDecoration);
	}

	public void refreshTargetDecoration() {
		FeatureConnection connectionModel = getConnectionModel();
		IGraphicalFeature target = connectionModel.getTarget();
		RotatableDecoration targetDecoration = null;
		if (target.getTree().getNumberOfChildren() > 1) {
			IGraphicalFeature source = connectionModel.getSource();
			final IFeatureStructure structure = target.getObject().getStructure();
			if (FeatureUIHelper.hasVerticalLayout(target.getGraphicalModel())) {
				if (!structure.isAnd() && (structure.getChildIndex(source.getObject().getStructure()) == (structure.getChildrenCount() - 1))) {
					targetDecoration = new RelationDecoration(structure.isMultiple(), target.getTree().getChildren().get(0).getObject());
				}
			} else {
				if (!structure.isAnd() && structure.isFirstChild(source.getObject().getStructure()))
					targetDecoration = new RelationDecoration(structure.isMultiple(), target.getTree().getChildren().get(target.getTree().getNumberOfChildren() - 1).getObject());
			}
		}

		PolylineConnection connection = (PolylineConnection) getConnectionFigure();
		connection.setTargetDecoration(targetDecoration);
	}

	public void refreshToolTip() {
		IFeature target = getConnectionModel().getTarget().getObject();
		toolTipContent.removeAll();
		toolTipContent.setLayoutManager(new GridLayout());
		toolTipContent.add(new Label(" Connection type: \n" + (target.getStructure().isAnd() ? " And" : (target.getStructure().isMultiple() ? " Or" : " Alternative"))));

		// call of the FeatureDiagramExtensions
		for (FeatureDiagramExtension extension : FeatureDiagramExtension.getExtensions()) {
			toolTipContent = extension.extendConnectionToolTip(toolTipContent, this);
		}

		((PolylineConnection) getConnectionFigure()).setToolTip(toolTipContent);
	}

	@Override
	public void activate() {
		//TODO _interfaces Removed Code
		getConnectionModel().addListener(this);
//		getConnectionModel().getSource().addListener(this);
		super.activate();
	}

	@Override
	public void deactivate() {
		super.deactivate();
		//TODO _interfaces Removed Code
		getConnectionModel().removeListener(this);
//		getConnectionModel().getSource().removeListener(this);
	}

	public void propertyChange(PropertyChangeEvent event) {
		String prop = event.getPropertyName();
		if (PARENT_CHANGED.equals(prop)) {
			refreshParent();
		} else if (MANDATORY_CHANGED.equals(prop)) {
			refreshSourceDecoration();
		}
	}

	/**
	 * Checks if the target and source features are from an external feature
	 * model.
	 * 
	 * @return true if both features are from an external feature model
	 */
	private boolean connectsExternFeatures() {
		FeatureConnection featureConnection = getConnectionModel();
		final IFeature source = featureConnection.getSource().getObject();
		final IFeature target = featureConnection.getTarget().getObject();
		return (source instanceof ExtendedFeature && ((ExtendedFeature) source).isFromExtern()
				&& target instanceof ExtendedFeature && ((ExtendedFeature) target).isFromExtern());
	}

}
