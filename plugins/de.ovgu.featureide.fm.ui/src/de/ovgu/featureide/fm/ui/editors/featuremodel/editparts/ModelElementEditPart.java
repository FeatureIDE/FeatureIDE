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

import org.eclipse.gef.editparts.AbstractGraphicalEditPart;

import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.ui.editors.IGraphicalElement;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.ModelElementFigure;

/**
 * An edit part for feature model elements, meaning features and constraints.
 *
 * @author Timo G&uuml;nther
 */
public abstract class ModelElementEditPart extends AbstractGraphicalEditPart implements IEventListener {

	@Override
	public ModelEditPart getParent() {
		return (ModelEditPart) super.getParent();
	}

	@Override
	public IGraphicalElement getModel() {
		return (IGraphicalElement) super.getModel();
	}

	@Override
	public ModelElementFigure getFigure() {
		return (ModelElementFigure) super.getFigure();
	}
}
