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
package de.ovgu.featureide.fm.ui.editors.featuremodel.figures;

import org.eclipse.draw2d.FreeformLayer;
import org.eclipse.draw2d.FreeformLayout;
import org.eclipse.draw2d.MarginBorder;

import de.ovgu.featureide.fm.core.explanations.Explanation;

/**
 * A figure representing the feature model.
 * 
 * @author Timo Guenther
 */
public class ModelFigure extends FreeformLayer {
	/** the currently active explanation */
	private Explanation activeExplanation;
	
	/**
	 * Constructs a new instance of this class.
	 */
	public ModelFigure() {
		setLayoutManager(new FreeformLayout());
		setBorder(new MarginBorder(5));
	}
	
	/**
	 * Returns the currently active explanation.
	 * This is the one explaining the defect of the feature that is currently being hovered over.
	 * @return
	 */
	public Explanation getActiveExplanation() {
		return activeExplanation;
	}
	
	/**
	 * Sets the currently active explanation.
	 * @param activeExplanation the currently active explanation
	 */
	public void setActiveExplanation(Explanation activeExplanation) {
		this.activeExplanation = activeExplanation;
	}
}