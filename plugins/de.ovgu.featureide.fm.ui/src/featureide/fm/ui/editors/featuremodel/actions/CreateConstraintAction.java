/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.viewers.IStructuredSelection;

import featureide.fm.core.FeatureModel;

/**
 * Creates a new propositional constraint below the feature diagram.
 * 
 * @author Christian Becker
 * @author Thomas Thuem
 */
public class CreateConstraintAction extends AbstractConstraintEditorAction {

	public CreateConstraintAction(GraphicalViewerImpl viewer,
			FeatureModel featuremodel, String menuname) {
		super(viewer, featuremodel, menuname);
	}

	@Override
	protected boolean isValidSelection(IStructuredSelection selection) {		
//		Iterator<?> iter = selection.iterator();
//		while (iter.hasNext()) {
//			Object editPart = iter.next();
//			if ((editPart instanceof ConstraintEditPart) || (editPart instanceof FeatureEditPart) ) {
//				return false;
//			}
//		}
		return true;
	}

	@Override
	public void run() {
		super.run();
		openEditor(null);
	}

}
