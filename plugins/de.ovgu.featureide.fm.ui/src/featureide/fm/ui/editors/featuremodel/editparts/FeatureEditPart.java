/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package featureide.fm.ui.editors.featuremodel.editparts;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.List;
import java.util.Map;

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

import featureide.fm.core.Feature;
import featureide.fm.core.FeatureConnection;
import featureide.fm.core.FeatureModel;
import featureide.fm.core.PropertyConstants;
import featureide.fm.ui.editors.FeatureUIHelper;
import featureide.fm.ui.editors.featuremodel.commands.renaming.FeatureCellEditorLocator;
import featureide.fm.ui.editors.featuremodel.commands.renaming.FeatureLabelEditManager;
import featureide.fm.ui.editors.featuremodel.figures.FeatureFigure;
import featureide.fm.ui.editors.featuremodel.policies.FeatureDirectEditPolicy;

/**
 * An editpart for features. It implements the <code>NodeEditPart</code> that
 * the models of features can provide connection anchors.
 * 
 * @author Thomas Thuem
 */
public class FeatureEditPart extends AbstractGraphicalEditPart implements NodeEditPart, PropertyConstants, PropertyChangeListener {
	
	public FeatureEditPart(Feature feature) {
		super();
		setModel(feature);
	}
	
	public Feature getFeatureModel() {
		return (Feature) getModel();
	}
	
	public FeatureFigure getFeatureFigure() {
		return (FeatureFigure) getFigure();
	}
	
	@Override
	protected IFigure createFigure() {
		FeatureFigure figure = new FeatureFigure(getFeatureModel());
		return figure;
	}

	@Override
	protected void createEditPolicies() {
		FeatureModel featureModel = ((ModelEditPart) getParent()).getFeatureModel();
		installEditPolicy(EditPolicy.DIRECT_EDIT_ROLE, new FeatureDirectEditPolicy(featureModel, getFeatureModel()));
	}
	
	private DirectEditManager manager;
	
	@Override
	public void performRequest(Request request) {
		if (request.getType() == RequestConstants.REQ_DIRECT_EDIT) {
			if (manager == null) {
				ModelEditPart parent = (ModelEditPart) getParent();
				FeatureModel featureModel = parent.getFeatureModel();
				manager = new FeatureLabelEditManager(this, TextCellEditor.class,
						new FeatureCellEditorLocator(getFeatureFigure()), featureModel);
			}
			manager.show();
		}
		else if (request.getType() == RequestConstants.REQ_OPEN) {
			Feature feature = getFeatureModel();
			feature.setMandatory(!feature.isMandatory());

			ModelEditPart parent = (ModelEditPart) getParent();
			FeatureModel featureModel = parent.getFeatureModel();
			featureModel.handleModelDataChanged();
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
		return ((FeatureFigure) figure).getSourceAnchor();
	}

	public ConnectionAnchor getSourceConnectionAnchor(Request request) {
		return ((FeatureFigure) figure).getSourceAnchor();
	}

	public ConnectionAnchor getTargetConnectionAnchor(org.eclipse.gef.ConnectionEditPart connection) {
		return ((FeatureFigure) figure).getTargetAnchor();
	}

	public ConnectionAnchor getTargetConnectionAnchor(Request request) {
		return ((FeatureFigure) figure).getTargetAnchor();
	}

	@Override
	public void activate() {
		getFeatureModel().addListener(this);
		super.activate();
	}
	
	@Override
	public void deactivate() {
		super.deactivate();
		getFeatureModel().removeListener(this);
	}

	/*
	 * (non-Javadoc)
	 * @see java.beans.PropertyChangeListener#propertyChange(java.beans.PropertyChangeEvent)
	 */
	@SuppressWarnings("unchecked")
	public void propertyChange(PropertyChangeEvent event) {
		String prop = event.getPropertyName();
		if (prop.equals(LOCATION_CHANGED)) {
			getFeatureFigure().setLocation((Point) event.getNewValue());
		}
		else if (prop.equals(CHILDREN_CHANGED)) {
			getFeatureFigure().setAbstract(getFeatureModel().isAbstract());
			for (FeatureConnection connection : getFeatureModel().getTargetConnections()) {
				Map registry = getViewer().getEditPartRegistry();
				ConnectionEditPart connectionEditPart = (ConnectionEditPart) registry.get(connection);
				if (connectionEditPart != null) {
					connectionEditPart.refreshSourceDecoration();
					connectionEditPart.refreshTargetDecoration();
					connectionEditPart.refreshToolTip();
				}
			}
		}
		else if (prop.equals(NAME_CHANGED)) {
			getFeatureFigure().setName(getFeatureModel().getName());
			FeatureUIHelper.setSize(getFeatureModel(),getFeatureFigure().getSize());
		}
	}
	
}
