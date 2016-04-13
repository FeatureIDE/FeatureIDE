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
package de.ovgu.featureide.ui.ahead.views.outline.jak;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.ui.part.FileEditorInput;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTModelElement;


/**
 * This class is part of the outline. It provides the content that
 * should be displayed. Therefor it maps the information provided
 * by the jakprojectmodel to the methods of the ITreeContentProvider
 * interface.
 * 
 * @author Tom Brosch
 * @author Thomas Thuem
 * @author Constanze Adler
 */
public class JakTreeContentProvider implements ITreeContentProvider {
	
	private IFile jakfile = null;

	private FSTModel jakProject = null;

	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof FSTModelElement)
			return ((FSTModelElement) parentElement).getChildren();
		return null;
	}

	public Object getParent(Object element) {
		if (element instanceof FSTModelElement)
			((FSTModelElement) element).getParent();
		return null;
	}

	public boolean hasChildren(Object element) {
		if (element instanceof FSTModelElement)
			return ((FSTModelElement) element).hasChildren();
		return false;
	}

	public Object[] getElements(Object inputElement) {
		IFeatureProject featureProject = CorePlugin.getFeatureProject(jakfile);
		if (featureProject == null)
			return null;
		
		String [] errMessage;
		String feature = featureProject.getFeatureName(jakfile);
		if (feature == null) {
			errMessage = new String[] {
					"No data to display available.",
					"Jakfile is no sourcefile"
			};
		} else {
			errMessage = new String[] {
				"No data to display available."
			};
		}

		jakProject = featureProject.getFSTModel();
		if (jakProject == null) {
			featureProject.getComposer().initialize(featureProject);
			featureProject.getComposer().buildFSTModel();
			jakProject = featureProject.getFSTModel();
		}
		if (jakProject != null) {
			FSTClass c = jakProject.getClass(jakfile);
			if (c != null)
				return new FSTClass[] { jakProject.getClass(jakfile) };
			else
				return errMessage;
		}

		return errMessage; //ticket #99 old code: return null;
	}

	public void dispose() {
	}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		if (newInput != null && newInput instanceof FileEditorInput) {
			IFile file = ((FileEditorInput) newInput).getFile();
			IFeatureProject featureProject = CorePlugin.getFeatureProject(file);
			if (featureProject != null) {
				jakfile = file;
				jakProject = featureProject.getFSTModel();
			}
		}
	}
}
