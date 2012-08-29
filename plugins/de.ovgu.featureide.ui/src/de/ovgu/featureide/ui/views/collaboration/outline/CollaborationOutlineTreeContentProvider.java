/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.ui.views.collaboration.model.Class;
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
	private Comparator<? super FSTDirective> directiveComparator = new Comparator<FSTDirective>(){

		@Override
		public int compare(FSTDirective o1, FSTDirective o2) {
			return o1.getStartLine() > o2.getStartLine() ? 1 : 0;
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
			if (model != null)
				if (model.getClass(((IFile) inputElement).getName()) != null)
					return new Object[] { model.getClass(((IFile) inputElement).getName()) };
				else
					return new String[] { "An outline is not available." };
			else
				return new String[] { "Collaboration Model not found" };
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
		
		if (parentElement instanceof Class) {
			// get all fields and methods
			HashMap<String, FSTMethod> methods = new HashMap<String, FSTMethod>();
			for (Role role : ((Class) parentElement).getRoles()) {
				for (FSTMethod m : role.methods) {
					String methodName = m.getName();
					if (!methods.containsKey(methodName)) {
						methods.put(methodName, m.copy());
					} else {
						methods.get(methodName).setOwn(m.getOwnFile());
					}
				}
			}
			FSTMethod[] methodArray = new FSTMethod[methods.size()];
			int i = 0;
			for (FSTMethod m : methods.values()) {
				methodArray[i] = m;
				i++;
			}
			
			HashMap<String, FSTField> fields = new HashMap<String, FSTField>();
			for (Role role : ((Class) parentElement).getRoles()) {
				for (FSTField f : role.fields) {
					String fieldName = f.getName();
					if (!fields.containsKey(fieldName)) {
							fields.put(fieldName, f.copy());
					} else {
						fields.get(fieldName).setOwn(f.getOwnFile());
					}
				}
			}
			FSTField[] fieldArray = new FSTField[fields.size()];
			i = 0;
			for (FSTField f : fields.values()) {
				fieldArray[i] = f;
				i++;
			}
			
			LinkedList<FSTDirective> directives = new LinkedList<FSTDirective>();
			for (Role role : ((Class) parentElement).getRoles()) {
				for (FSTDirective d : role.directives) {
					if (d.getParent() == null) {
						directives.add(d);
					}
				}
			}
			FSTDirective[] directiveArray = new FSTDirective[directives.size()];
			i = 0;
			for (FSTDirective f : directives) {
				directiveArray[i] = f;
				i++;
			}
			
			Arrays.sort(methodArray, methodComparator);
			Arrays.sort(fieldArray, fieldComparator);
			Arrays.sort(directiveArray, directiveComparator);
			
			Object[] obj = new Object[fieldArray.length + methodArray.length + directiveArray.length];

			for (i = 0; i < fieldArray.length; i++) {
				obj[i] = fieldArray[i];
			}
			i = 0;
			for (int j = fieldArray.length; i < methodArray.length; i++, j++) {
				obj[j] = methodArray[i];
			}
			i = 0;
			for (int j = fieldArray.length + methodArray.length; i < directiveArray.length; i++, j++) {
				obj[j] = directiveArray[i];
			}
			
			return obj;
		} else if (parentElement instanceof FSTMethod) {
			// get all the roles that belong to a method
			LinkedList<Role> roleList = new LinkedList<Role>();
			List<Role> roles = model.getRoles();
			for (Role role : roles) {
				for (FSTMethod m : role.methods) {
					if (m.isOwn(role.file) && ((FSTMethod)parentElement).isOwn(role.file) &&
							m.getName().equals(((FSTMethod)parentElement).getName())) {
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
				for (FSTField f : role.fields) {
					if (f.isOwn(role.file) && ((FSTField)parentElement).isOwn(role.file) &&
							f.getName().equals(((FSTField)parentElement).getName())) {
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
		} else if (parentElement instanceof FSTDirective) {
			FSTDirective[] directiveArray = ((FSTDirective)parentElement).getChildren().clone();
			Arrays.sort(directiveArray, directiveComparator);
			return directiveArray;
		}
		return new Role[0];
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
		if (element instanceof Class) {
			for (Role role :((Class) element).getRoles()) {
				if (role.methods.size() > 0 || role.fields.size() > 0 ||
						role.directives.size() > 0) {
					return true;
				}
			}
			return false;
		}

		if (element instanceof FSTMethod)
			return true;

		if (element instanceof FSTField)
			return true;
		
		if (element instanceof FSTDirective) {
			return ((FSTDirective)element).getChildren().length != 0;
		}

		return false;
	}

}
