/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import org.eclipse.swt.SWT;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;

/**
 * Renames a particular feature at the feature diagram.
 * 
 * @author Tom Brosch
 */
public class RenameAction extends SingleSelectionAction {

	public static final String ID = "de.ovgu.featureide.rename";
	private Object diagramEditor;

	public RenameAction(Object viewer, FeatureModel featureModel, Object graphicalViewer) {
		super("Rename (F2)", viewer);
		this.setAccelerator(SWT.F2);
		this.diagramEditor = graphicalViewer;
	}

	@Override
	public void run() {
		FeatureEditPart part = getSelectedFeatureEditPart(diagramEditor);
		part.showRenameManager();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.fm.ui.editors.featuremodel.actions.SingleSelectionAction
	 * #updateProperties()
	 */
	@Override
	protected void updateProperties() {
		setChecked(false);
		setEnabled(true);
	}

}
