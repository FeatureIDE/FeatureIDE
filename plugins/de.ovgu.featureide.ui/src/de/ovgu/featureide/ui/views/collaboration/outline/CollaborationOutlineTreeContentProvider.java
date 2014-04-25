package de.ovgu.featureide.ui.views.collaboration.outline;

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

import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTContractedRole;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTInvariant;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.fstmodel.RoleElement;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;

/**
 * Provides the content for the collaboration outline.
 * 
 * @author Jan Wedding
 * @author Melanie Pflaume
 * @author Stefan Krüger
 * @author Florian Proksch
 */
public class CollaborationOutlineTreeContentProvider implements ITreeContentProvider {

	protected FSTModel model;

	public CollaborationOutlineTreeContentProvider() {
	}

	private Comparator<? super FSTInvariant> invariantComparator = new Comparator<FSTInvariant>() {

		@Override
		public int compare(FSTInvariant o1, FSTInvariant o2) {
			return o1.getName().compareToIgnoreCase(o2.getName());
		}

	};

	private Comparator<? super FSTMethod> methodComparator = new Comparator<FSTMethod>() {

		@Override
		public int compare(FSTMethod o1, FSTMethod o2) {
			return o1.getName().compareToIgnoreCase(o2.getName());
		}

	};

	private Comparator<? super FSTField> fieldComparator = new Comparator<FSTField>() {

		@Override
		public int compare(FSTField o1, FSTField o2) {
			return o1.getName().compareToIgnoreCase(o2.getName());
		}

	};

	private Comparator<? super FSTDirective> directiveComparator = new Comparator<FSTDirective>() {

		@Override
		public int compare(FSTDirective o1, FSTDirective o2) {
			return o1.getStartLine() > o2.getStartLine() ? 1 : 0;
		}

	};

	@Override
	public void dispose() {
	}

	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		if (newInput != null && (newInput instanceof IFile)) {
			IFeatureProject featureProject = CorePlugin.getFeatureProject((IFile) newInput);
			if (featureProject != null)
				model = featureProject.getFSTModel();// builder.buildCollaborationModel(featureProject);
		}
	}

	@Override
	public Object[] getElements(Object inputElement) {
		if (inputElement == null || !(inputElement instanceof IFile))
			return new String[] { "no file found" };

		IFile file = (IFile) inputElement;
		IFeatureProject featureProject = CorePlugin.getFeatureProject(file);
		
		if (featureProject != null) {
			model = featureProject.getFSTModel();

			if (model != null) {
//	TODO: Change composers to use the full path instead of filename (with the same separator on every platform)
//				IPath filePath = file.getProjectRelativePath();
//				IPath featurePath = featureProject.getSourceFolder().getProjectRelativePath();
//				filePath = filePath.removeFirstSegments(filePath.matchingFirstSegments(featurePath) + 1);
//				String classString = filePath.toString();
//				FSTClass c = model.getClass(classString);
				FSTClass c = model.getClass(file.getName());
				if (c != null) {
					return new Object[] { c };
				}
			}
		}
		return new String[] { "Collaboration Model not found" };
	}

	@Override
	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof FSTClass) {
			// get all fields, methods, directives and invariants
			LinkedList<FSTMethod> methods = new LinkedList<FSTMethod>();
			LinkedList<FSTField> fields = new LinkedList<FSTField>();
			LinkedList<FSTInvariant> invariants = new LinkedList<FSTInvariant>();
			LinkedList<FSTDirective> directives = new LinkedList<FSTDirective>();
			for (FSTRole role : ((FSTClass) parentElement).getRoles()) {
				invariants.addAll(role.getClassFragment().getInvariants());
				methods.addAll(role.getClassFragment().getMethods());
				fields.addAll(role.getClassFragment().getFields());
				directives.addAll(role.getDirectives());
			}

			LinkedList<RoleElement> obj = new LinkedList<RoleElement>();
			Collections.sort(methods, methodComparator);
			Collections.sort(fields, fieldComparator);
			Collections.sort(directives, directiveComparator);
			Collections.sort(invariants, invariantComparator);
			obj.addAll(invariants);
			obj.addAll(fields);
			obj.addAll(methods);
			// Remove duplicates
			LinkedList<RoleElement> remDup = new LinkedList<RoleElement>();
			for (int i = 0; i < obj.size(); i++) {
				if (remDup.isEmpty() || !remDup.getLast().getName().equals(obj.get(i).getName())) {
					remDup.add(obj.get(i));
				}
			}
			
			LinkedList<FSTDirective> remDupDir = new LinkedList<FSTDirective>();
			for (int i = 0; i < directives.size(); i++) {
				if (remDupDir.isEmpty() || !remDupDir.contains(directives.get(i))) {
					remDupDir.add(directives.get(i));
				}
			}
			
			remDup.addAll(remDupDir);
			return (remDup.toArray());
		} else if (parentElement instanceof FSTMethod) {
			// get all the roles that belong to a method
			List<FSTRole> roleList = new LinkedList<FSTRole>();

			for (FSTRole role : ((FSTMethod) parentElement).getRole().getFSTClass().getRoles()) {
				for (FSTMethod m : role.getClassFragment().getMethods()) {
					if (// m.isOwn(role.file) &&
						// ((FSTMethod)parentElement).isOwn(role.file) &&
					m.getFullName().equals(((FSTMethod) parentElement).getFullName())) {
						if (m.hasContract()) {
							roleList.add(new FSTContractedRole(role.getFile(), role.getFeature(), role.getFSTClass()));
						} else {
							roleList.add(role);
						}
						break;
					}
				}
			}

			List<String> featureOrder = CorePlugin.getFeatureProject(((FSTMethod) parentElement).getRole().getFile()).getFeatureModel().getFeatureOrderList();

			FSTRole[] obj = new FSTRole[roleList.size()];
			int index = 0;
			for (int i = 0; i < featureOrder.size(); i++) {
				for (int j = 0; j < roleList.size(); j++) {
					if (roleList.get(j).getFeature().getName().equals(featureOrder.get(i))) {
						obj[index++] = roleList.get(j);
						break;
					}

				}
			}
			return obj;
		} else if (parentElement instanceof FSTInvariant) {
			// get all the roles that belong to an inavariant
			LinkedList<FSTRole> roleList = new LinkedList<FSTRole>();
			for (FSTRole role : ((FSTInvariant) parentElement).getRole().getFSTClass().getRoles()) {
				for (FSTInvariant i : role.getClassFragment().getInvariants()) {
					if (((FSTInvariant) parentElement).getFullName().equals(i.getFullName())) {
						roleList.add(role);
						break;
					}
				}
			}

			FSTRole[] obj = new FSTRole[roleList.size()];
			for (int i = 0; i < roleList.size(); i++) {
				obj[i] = roleList.get(i);
			}

			return (roleList.toArray());
		} else if (parentElement instanceof FSTField) {
			// get all the roles that belong to a field
			LinkedList<FSTRole> roleList = new LinkedList<FSTRole>();
			for (FSTRole role : ((FSTField) parentElement).getRole().getFSTClass().getRoles()) {
				for (FSTField f : role.getClassFragment().getFields()) {
					if (f.getFullName().equals(((FSTField) parentElement).getFullName())) {
						roleList.add(role);
						break;
					}
				}
			}

			FSTRole[] obj = new FSTRole[roleList.size()];
			for (int i = 0; i < roleList.size(); i++) {
				obj[i] = roleList.get(i);
			}

			return obj;
		} else if (parentElement instanceof FSTDirective) {
			FSTDirective[] directiveArray = ((FSTDirective) parentElement).getChildren().clone();
			Arrays.sort(directiveArray, directiveComparator);
			return directiveArray;
		}
		return new FSTRole[0];
	}

	@Override
	public Object getParent(Object element) {
		return null;
	}

	@Override
	public boolean hasChildren(Object element) {
		if (element instanceof FSTClass) {
			for (FSTRole role : ((FSTClass) element).getRoles()) {
				if (!role.getClassFragment().getMethods().isEmpty() || !role.getClassFragment().getFields().isEmpty() || !role.getDirectives().isEmpty()) {
					return true;
				}
			}
			return false;
		}

		if (element instanceof FSTMethod)
			return true;

		if (element instanceof FSTField)
			return true;

		if (element instanceof FSTInvariant)
			return true;

		if (element instanceof FSTDirective) {
			return ((FSTDirective) element).getChildren().length != 0;
		}

		return false;
	}
}
