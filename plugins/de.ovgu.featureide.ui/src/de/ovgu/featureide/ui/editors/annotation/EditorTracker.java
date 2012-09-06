/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.ui.editors.annotation;

import java.util.HashSet;

import org.eclipse.ui.IPartListener2;
import org.eclipse.ui.IWindowListener;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartReference;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.texteditor.ITextEditor;

/**
 * Listens for an editorpart to attach the color annotation model
 * 
 * @author Sebastian Krieter
 */
public class EditorTracker {

	private final IWorkbench workbench;
	private HashSet<IWorkbenchPartReference> annotatedPartrefSet = new HashSet<IWorkbenchPartReference>();

	private IWindowListener windowListener = new IWindowListener() {
		public void windowOpened(IWorkbenchWindow window) {
			window.getPartService().addPartListener(partListener);
		}

		public void windowClosed(IWorkbenchWindow window) {
			window.getPartService().removePartListener(partListener);
		}

		public void windowActivated(IWorkbenchWindow window) {
		}

		public void windowDeactivated(IWorkbenchWindow window) {
		}
	};

	private IPartListener2 partListener = new IPartListener2() {
		public void partOpened(IWorkbenchPartReference partref) {
			annotateEditor(partref);
		}

		public void partActivated(IWorkbenchPartReference partref) {
			if (annotatedPartrefSet.contains(partref)) {
				updateEditor(partref);
			}
		}

		public void partBroughtToTop(IWorkbenchPartReference partref) {
		}

		public void partVisible(IWorkbenchPartReference partref) {
		}

		public void partInputChanged(IWorkbenchPartReference partref) {
		}

		public void partClosed(IWorkbenchPartReference partref) {
		}

		public void partDeactivated(IWorkbenchPartReference partref) {
		}

		public void partHidden(IWorkbenchPartReference partref) {
		}
	};

	public EditorTracker(IWorkbench workbench) {
		this.workbench = workbench;
		for (final IWorkbenchWindow w : workbench.getWorkbenchWindows()) {
			w.getPartService().addPartListener(partListener);
		}
		workbench.addWindowListener(windowListener);
	}

	public void dispose() {
		workbench.removeWindowListener(windowListener);
		for (final IWorkbenchWindow w : workbench.getWorkbenchWindows()) {
			w.getPartService().removePartListener(partListener);
		}
		annotatedPartrefSet.clear();
	}

	private void annotateEditor(IWorkbenchPartReference partref) {
		IWorkbenchPart part = partref.getPart(false);
		if (part instanceof ITextEditor) {
			if (ColorAnnotationModel.attach((ITextEditor) part)) {
				annotatedPartrefSet.add(partref);
			}
		}
	}
	
	private void updateEditor(IWorkbenchPartReference partref) {
		IWorkbenchPart part = partref.getPart(false);
		if (part != null) {
			ITextEditor editor = (ITextEditor) part;
			ColorAnnotationModel.attach(editor);
		}
	}
}
