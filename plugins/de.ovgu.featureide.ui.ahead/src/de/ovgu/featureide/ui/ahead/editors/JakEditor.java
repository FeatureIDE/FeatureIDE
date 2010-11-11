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
package de.ovgu.featureide.ui.ahead.editors;

import org.eclipse.core.resources.IFile;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.ui.ahead.AheadUIPlugin;
import de.ovgu.featureide.ui.ahead.editors.jak.JakConfiguration;
import de.ovgu.featureide.ui.ahead.editors.jak.JakDocumentProvider;
import de.ovgu.featureide.ui.ahead.views.outline.JakOutlinePage;

/**
 * An editor for Jak files that supports the Jak-specific keywords.
 * 
 * @author Marcus Leich
 *
 */
public class JakEditor extends TextEditor {
	
	public static final String ID = AheadUIPlugin.PLUGIN_ID + ".editors.JakEditor";

	private static final Image DERIVED_IMAGE = AheadUIPlugin.getImage("sample.gif");
	
	private JakOutlinePage outlinePage;

	public JakEditor() {
		super();
		setSourceViewerConfiguration(new JakConfiguration());
		setDocumentProvider(new JakDocumentProvider());
	}

	@Override
	public void init(IEditorSite site, IEditorInput input)
			throws PartInitException {
		super.init(site, input);
		if (input instanceof IFileEditorInput) {
			IFile file = ((IFileEditorInput) input).getFile();
			IFeatureProject featureProject = CorePlugin.getFeatureProject(file);

			// check that the project is a FeatureIDE project and registered
			if (featureProject == null)
				return;
			String feature = featureProject.getFeatureName(file);
			if (feature != null)
				setPartName(file.getName() + "[" + feature + "]");
			else {
				String equation = featureProject.getEquationName(file);
				if (equation != null)
					setPartName(file.getName() + "<" + equation + ">");
				setTitleImage(DERIVED_IMAGE);
			}
		}
	}

	@SuppressWarnings("rawtypes")
	public Object getAdapter(Class required) {
		if (IContentOutlinePage.class.equals(required)) {
			if (outlinePage == null) {
				outlinePage = new JakOutlinePage(getDocumentProvider(), this);
				outlinePage.setInput(getEditorInput());
			}
			return outlinePage;
		}
		return super.getAdapter(required);
	}
	
	
	/* update Outline after build process*/
	public void setFocus(){
		if (outlinePage!=null){
			outlinePage.setInput(getEditorInput());
			outlinePage.update();
		}
		super.setFocus();
	}
	
}
