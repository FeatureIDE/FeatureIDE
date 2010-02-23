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
package featureide.fm.ui.editors.featuremodel.actions;

import java.util.Iterator;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.viewers.IStructuredSelection;

import featureide.fm.core.FeatureModel;
import featureide.fm.core.io.guidsl.FeatureModelWriter;
import featureide.fm.ui.editors.featuremodel.editparts.ConstraintEditPart;
import featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;

/**
 * TODO description
 * 
 * @author Christian Becker
 */
public class InsertConstraintAction extends AbstractConstraintEditorAction {

	/**
	 * @param viewer
	 * @param featuremodel
	 */
	public InsertConstraintAction(GraphicalViewerImpl viewer,
			FeatureModel featuremodel, String menuname) {
		super(viewer, featuremodel, menuname);
	}

	/* (non-Javadoc)
	 * @see featureide.fm.ui.editors.AbstractConstraintEditor#editorhook()
	 */
	
//	protected void editorhook() {
		
		
	

	/* (non-Javadoc)
	 * @see featureide.fm.ui.editors.AbstractConstraintEditor#isValidSelection(org.eclipse.jface.viewers.IStructuredSelection)
	 */
	@Override
	protected boolean isValidSelection(IStructuredSelection selection) {		
		Iterator<?> iter = selection.iterator();
		while (iter.hasNext()) {
			Object editPart = iter.next();
			if ((editPart instanceof ConstraintEditPart) || (editPart instanceof FeatureEditPart) ) {
				return false;
			}
		}
		return true;
		
	}

	/* (non-Javadoc)
	 * @see featureide.fm.ui.editors.AbstractConstraintEditor#run()
	 */
	@Override
	public void run() {
		writer = new FeatureModelWriter(featuremodel);
		featuretext = writer.writeToString();
		createEditor("Insert propositional constraint");
		
	}

}
