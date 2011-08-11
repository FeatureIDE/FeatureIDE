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
package de.ovgu.featureide.ui.views.collaboration.outline;

import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.ui.views.collaboration.model.CollaborationModel;
import de.ovgu.featureide.ui.views.collaboration.model.CollaborationModelBuilder;
import de.ovgu.featureide.ui.views.collaboration.model.Role;

/**
 * provides the content for the collaboration outline
 * 
 * @author Jan Wedding
 * @author Melanie Pflaume
 */
public class CollaborationOutlineTreeContentProvider implements
		ITreeContentProvider {

	private CollaborationModel model;
	private CollaborationModelBuilder builder = new CollaborationModelBuilder();
	private Comparator<? super FSTMethod> methodComparator = new Comparator<FSTMethod>() {


		@Override
		public int compare(FSTMethod o1, FSTMethod o2) {
			return o1.getName().compareToIgnoreCase(o2.getName());
		}

	};
	private Comparator<? super FSTField> fieldComparator = new Comparator<FSTField>(){

		@Override
		public int compare(FSTField o1, FSTField o2) {
			return o1.getName().compareToIgnoreCase(o2.getName());
		}
		
	};

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.viewers.IContentProvider#dispose()
	 */
	@Override
	public void dispose() {
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.jface.viewers.IContentProvider#inputChanged(org.eclipse.jface
	 * .viewers.Viewer, java.lang.Object, java.lang.Object)
	 */
	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		if (newInput != null && (newInput instanceof IFile)) {
			IFeatureProject featureProject = CorePlugin
					.getFeatureProject((IFile) newInput);
			if (featureProject != null)
				model = builder.buildCollaborationModel(featureProject);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.jface.viewers.ITreeContentProvider#getElements(java.lang.
	 * Object)
	 */
	@Override
	public Object[] getElements(Object inputElement) {
		if (inputElement == null || !(inputElement instanceof IFile))
			return new String[] { "no file found" };

		IFeatureProject featureProject = CorePlugin
				.getFeatureProject((IFile) inputElement);
		if (featureProject != null)
			if (featureProject.getFSTModel() != null)
				if (featureProject.getFSTModel().getClass((IFile) inputElement) != null)
					return new Object[] { featureProject.getFSTModel()
							.getClass((IFile) inputElement) };
				else
					return new String[] { "Class in FSTModel not found" };
			else
				return new String[] { "FSTModel not found" };
		else
			return new String[] { "This is no feature project" };
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.jface.viewers.ITreeContentProvider#getChildren(java.lang.
	 * Object)
	 */
	@Override
	public Object[] getChildren(Object parentElement) {
		
		if (parentElement instanceof FSTClass) {
			// get all fields and methods
			FSTMethod[] methods = ((FSTClass) parentElement).getMethods();
			FSTField[] fields = ((FSTClass) parentElement).getFields();
			int methodCount = ((FSTClass) parentElement).getMethodCount();
			int fieldCount = ((FSTClass) parentElement).getFieldCount();
			
			Arrays.sort(methods, methodComparator);
			Arrays.sort(fields, fieldComparator);
			Object[] obj = new Object[methodCount + fieldCount];

			for (int i = 0; i < fieldCount; i++) {
				obj[i] = fields[i];
			}
			
			for (int i = 0, j = fieldCount; i < methodCount; i++, j++) {
				obj[j] = methods[i];
			}
			
			return obj;
			
		} else if (parentElement instanceof FSTMethod) {
			// get all the roles that belong to a method
			LinkedList<Role> roleList = new LinkedList<Role>();
			List<Role> roles = model.getRoles();
			for (Role role : roles) {
				for (FSTMethod m : role.methods) {
					if (m.isOwn(role.file) && m.equals(parentElement)) {
						roleList.add(role);
						break;
					}
				}
			}

			Role[] obj = new Role[roleList.size()];
			for (int i = 0; i < roleList.size(); i++) {
				obj[i] = roleList.get(i);
			}
			return obj;
			
		} else if (parentElement instanceof FSTField) {
			// get all the roles that belong to a field
			LinkedList<Role> roleList = new LinkedList<Role>();
			List<Role> roles = model.getRoles();
			for (Role role : roles) {
				for (FSTField m : role.fields) {
					if (m.isOwn(role.file) && m.equals(parentElement)) {
						roleList.add(role);
						break;
					}
				}
			}

			Role[] obj = new Role[roleList.size()];
			for (int i = 0; i < roleList.size(); i++) {
				obj[i] = roleList.get(i);
			}

			return obj;
		}
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.jface.viewers.ITreeContentProvider#getParent(java.lang.Object
	 * )
	 */
	@Override
	public Object getParent(Object element) {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.jface.viewers.ITreeContentProvider#hasChildren(java.lang.
	 * Object)
	 */
	@Override
	public boolean hasChildren(Object element) {
		if (element instanceof FSTClass)
			return (((FSTClass) element).getMethodCount() + ((FSTClass) element)
					.getFieldCount()) > 0;

		if (element instanceof FSTMethod)
			return true;

		if (element instanceof FSTField)
			return true;

		return false;
	}

}
