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
package de.ovgu.featureide.ui.ahead.views.outline.jak;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.ui.part.FileEditorInput;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.jakprojectmodel.IClass;
import de.ovgu.featureide.core.jakprojectmodel.IJakModelElement;
import de.ovgu.featureide.core.jakprojectmodel.IJakProjectModel;


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

	private IJakProjectModel jakProject = null;

	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof IJakModelElement)
			return ((IJakModelElement) parentElement).getChildren();

		return null;
	}

	public Object getParent(Object element) {
		if (element instanceof IJakModelElement)
			((IJakModelElement) element).getParent();
		return null;
	}

	public boolean hasChildren(Object element) {
		if (element instanceof IJakModelElement)
			return ((IJakModelElement) element).hasChildren();
		return false;
	}

	public Object[] getElements(Object inputElement) {
		IPath path = jakfile.getFullPath();
		String feature = path.segment(path.segmentCount()-2);
		
		String [] errMessage = new String[] {
			"No data to display available.",
			"Please choose a configuration",
			"where feature " +feature,
			"is selected and build this",
			"configuration." };
		
		if (jakProject != null) {
			IClass c = jakProject.getClass(jakfile);
			if (c != null)
				return new IClass[] { jakProject.getClass(jakfile) };
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
				jakProject = featureProject.getJakProjectModel();
			}
		}
	}
}
