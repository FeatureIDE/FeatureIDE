/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
import java.util.Collection;
import java.util.List;

import org.eclipse.draw2d.MouseEvent;
import org.eclipse.draw2d.MouseMotionListener;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.RootEditPart;
import org.eclipse.gef.editparts.AbstractGraphicalEditPart;

import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.Legend;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.ModelFigure;
import de.ovgu.featureide.fm.ui.editors.featuremodel.policies.ModelLayoutEditPolicy;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * The main editpart that has all <code>FeatureEditPart</code>s as children.
 * Notice that Draw2D calls a figure child of another when its drawn within the
 * parent figure. Therefore, all features need to by direct children of this
 * editpart.
 * 
 * @author Thomas Thuem
 * @author Marcus Pinnecke
 */
public class ModelEditPart extends AbstractGraphicalEditPart {
	/**
	 * Listens for mouse motion events to update the active explanation.
	 * 
	 * @author Timo Guenther
	 */
	private class ActiveExplanationMouseMotionListener implements MouseMotionListener {
		/** edit part of the listened figure */
		private final ModelElementEditPart editPart;
		
		/**
		 * Constructs a new instance of this class.
		 * @param editPart edit part of the listened figure
		 */
		public ActiveExplanationMouseMotionListener(ModelElementEditPart editPart) {
			this.editPart = editPart;
		}
		
		@Override
		public void mouseDragged(MouseEvent event) {}
		
		@Override
		public void mouseEntered(MouseEvent event) {}
		
		@Override
		public void mouseExited(MouseEvent event) {
			setActiveExplanation(null);
		}
		
		@Override
		public void mouseHover(MouseEvent event) {
			final IFeatureModelElement modelElement = editPart.getModel().getObject();
			final FeatureModelAnalyzer analyzer = getModel().getFeatureModel().getAnalyser();
			analyzer.addExplanation(modelElement);
			setActiveExplanation(analyzer.getExplanation(modelElement));
		}
		
		@Override
		public void mouseMoved(MouseEvent event) {}
		
		/**
		 * Sets the currently active explanation.
		 * @param activeExplanation new active explanation
		 */
		private void setActiveExplanation(Explanation activeExplanation) {
			final Explanation oldActiveExplanation = getFigure().getActiveExplanation();
			if (oldActiveExplanation == activeExplanation) {
				return;
			}
			getFigure().setActiveExplanation(activeExplanation);
			getModel().getFeatureModel().fireEvent(new FeatureIDEEvent(
					editPart.getModel().getObject(),
					EventType.ACTIVE_EXPLANATION_CHANGED,
					oldActiveExplanation,
					activeExplanation));
		}
	}

	ModelEditPart(IGraphicalFeatureModel featureModel) {
		setModel(featureModel);
	}

	public IGraphicalFeatureModel getFeatureModel() {
		return (IGraphicalFeatureModel) getModel();
	}
	
	@Override
	public RootEditPart getParent() {
		return (RootEditPart) super.getParent();
	}
	
	@Override
	public IGraphicalFeatureModel getModel() {
		return (IGraphicalFeatureModel) super.getModel();
	}
	
	@Override
	public ModelFigure getFigure() {
		return (ModelFigure) super.getFigure();
	}

	protected ModelFigure createFigure() {
		return new ModelFigure();
	}

	@Override
	protected void createEditPolicies() {
		installEditPolicy(EditPolicy.LAYOUT_ROLE, new ModelLayoutEditPolicy(getModel()));
	}

	@Override
	protected List<Object> getModelChildren() {
		final IGraphicalFeatureModel fm = getModel();

		final List<?> constraints = fm.getConstraints();
		final Collection<?> features = Functional.toList(fm.getFeatures());

		final ArrayList<Object> list = new ArrayList<>(constraints.size() + features.size() + 1);

		list.addAll(features);
		list.addAll(constraints);

		if (!FMPropertyManager.isLegendHidden()) {
			list.add(new Legend(fm));
		}

		return list;
	}

	@Override
	public EditPart createChild(Object model) {
		final EditPart child = super.createChild(model);
		if (child instanceof ModelElementEditPart) {
			final ModelElementEditPart c = (ModelElementEditPart) child;
			c.getFigure().addMouseMotionListener(new ActiveExplanationMouseMotionListener(c));
		}
		return child;
	}
}
