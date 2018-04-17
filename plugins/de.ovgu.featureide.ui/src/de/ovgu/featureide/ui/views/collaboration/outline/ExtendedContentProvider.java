/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.views.collaboration.outline;

import static de.ovgu.featureide.fm.core.localization.StringTable.NO_FILE_FOUND;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.StructuredViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerSorter;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTContractedRole;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTInvariant;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.fstmodel.IRoleElement;
import de.ovgu.featureide.core.fstmodel.RoleElement;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTModelForPP;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineTreeContentProvider;

/**
 * Provides the content for the collaboration outline.
 *
 * @author Jan Wedding
 * @author Melanie Pflaume
 * @author Stefan Kr�ger
 * @author Florian Proksch
 * @author Dominic Labsch
 * @author Daniel P�sche
 * @author Reimar Schr�ter
 */
public class ExtendedContentProvider extends OutlineTreeContentProvider {

	protected FSTModel model;

	public ExtendedContentProvider() {

	}

	@Override
	public void dispose() {}

	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		if ((newInput != null) && (newInput instanceof IFile)) {
			final IFeatureProject featureProject = CorePlugin.getFeatureProject((IFile) newInput);
			if (featureProject != null) {
				model = featureProject.getFSTModel();
			}

			if (viewer instanceof StructuredViewer) {
				((StructuredViewer) viewer).setSorter(new ViewerSorter() {

					/*
					 * (non-Javadoc)
					 * @see org.eclipse.jface.viewers.ViewerComparator#compare(org.eclipse.jface.viewers.Viewer, java.lang.Object, java.lang.Object)
					 */
					@Override
					public int compare(Viewer viewer, Object o1, Object o2) {
						final int startLineO1 = getLine(o1);
						final int startLineO2 = getLine(o2);

						return startLineO1 - startLineO2;
					}

					private int getLine(Object o1) {
						int startLineO1 = -1;

						if (o1 instanceof FSTDirective) {
							startLineO1 = ((FSTDirective) o1).getStartLine();
						} else if (o1 instanceof RoleElement<?>) {
							startLineO1 = ((RoleElement<?>) o1).getLine();
						}
						return startLineO1;
					}
				});
			}
		}
	}

	@Override
	public Object[] getElements(Object inputElement) {
		if ((inputElement == null) || !(inputElement instanceof IFile)) {
			return new String[] { NO_FILE_FOUND };
		}

		final IFile file = (IFile) inputElement;
		final IFeatureProject featureProject = CorePlugin.getFeatureProject(file);

		if (featureProject != null) {
			model = featureProject.getFSTModel();

			if ((model instanceof FSTModelForPP) && (((FSTModelForPP) model).getExtendedFst() != null)) {
				model = ((FSTModelForPP) model).getExtendedFst();
			}

			if (model != null) {
				final FSTClass c = model.getClass(model.getAbsoluteClassName(file));

				if (c != null) {
					return new Object[] { c };
				}
			}
		}
		return new String[] { "Create signature is not enabled" };
	}

	@Override
	public Object[] getChildren(Object parentElement) {
		Object[] obj = null;
		if (parentElement instanceof FSTClass) {
			// get all fields, methods, directives and invariants
			final TreeSet<FSTMethod> methods = new TreeSet<FSTMethod>();
			final TreeSet<FSTField> fields = new TreeSet<FSTField>();
			final TreeSet<FSTInvariant> invariants = new TreeSet<FSTInvariant>();
			final TreeSet<FSTDirective> directives = new TreeSet<FSTDirective>();
			final TreeSet<FSTClassFragment> innerClasses = new TreeSet<FSTClassFragment>();

			for (final FSTRole role : ((FSTClass) parentElement).getRoles()) {
				invariants.addAll(role.getClassFragment().getInvariants());
				for (final FSTMethod fstMethod : role.getMethods()) {
					if (fstMethod.getParent() instanceof FSTClassFragment) {
						methods.add(fstMethod);
					}
				}
				fields.addAll(role.getFields());
				final TreeSet<FSTDirective> roleDirectives = role.getDirectives();
				for (final FSTDirective directive : roleDirectives) {
					if (directive.getParent() == null) {
						directives.add(directive);
					}
				}
				innerClasses.addAll(role.getInnerClasses());
			}

			obj = new IRoleElement[methods.size() + fields.size() + invariants.size() + directives.size() + innerClasses.size()];
			int pos = 0;
			System.arraycopy(invariants.toArray(), 0, obj, pos, invariants.size());
			System.arraycopy(fields.toArray(), 0, obj, pos += invariants.size(), fields.size());
			System.arraycopy(methods.toArray(), 0, obj, pos += fields.size(), methods.size());
			System.arraycopy(directives.toArray(), 0, obj, pos += methods.size(), directives.size());
			System.arraycopy(innerClasses.toArray(), 0, obj, pos += directives.size(), innerClasses.size());

			return filter(obj);
		} else if (parentElement instanceof FSTMethod) {
			// get all the roles that belong to a method

			final Set<FSTRole> roleList = new HashSet<FSTRole>();
			final Set<FSTMethod> methods = new HashSet<FSTMethod>();
			for (final FSTRole role : ((FSTMethod) parentElement).getRole().getFSTClass().getRoles()) {
				for (final FSTMethod m : role.getAllMethods()) {
					if (// m.isOwn(role.file) &&
						// ((FSTMethod)parentElement).isOwn(role.file) &&
					m.getFullName().equals(((FSTMethod) parentElement).getFullName())) {
						if (m.hasContract()) {
							roleList.add(new FSTContractedRole(role.getFile(), role.getFeature(), role.getFSTClass()));
						} else {
							roleList.add(role);
						}
						methods.add(m);
						break;
					}
				}
			}

			final IFeatureProject project = CorePlugin.getFeatureProject(((FSTMethod) parentElement).getRole().getFile());
			Collection<String> featureOrder = new ArrayList<>();
			if (project != null) {
				featureOrder = project.getFeatureModel().getFeatureOrderList();
			}

			if (((FSTMethod) parentElement).getFSTDirectives().size() == 0) {
				obj = new FSTRole[roleList.size()];
				int index = 0;
				for (final String featureName : featureOrder) {

					for (final Iterator<FSTRole> it = roleList.iterator(); it.hasNext();) {
						final FSTRole next = it.next();
						if (next.getFeature().getName().equals(featureName)) {
							obj[index++] = next;
							it.remove();
							break;
						}
					}
				}
			} else {
				final List<FSTDirective> dirs = new ArrayList<>();
				for (final FSTRole role : roleList) {
					if (role.getMethods().contains(parentElement)) {
						// equals works correct?
						for (final FSTMethod method : role.getMethods()) {
							if (method.equals(parentElement)) {
								dirs.addAll(method.getFSTDirectives());
								break;
							}
						}
					}
				}
				return dirs.toArray();
			}

		} else if (parentElement instanceof FSTInvariant) {
			// get all the roles that belong to an invariant
			final LinkedList<FSTRole> roleList = new LinkedList<FSTRole>();
			for (final FSTRole role : ((FSTInvariant) parentElement).getRole().getFSTClass().getRoles()) {
				for (final FSTInvariant i : role.getClassFragment().getInvariants()) {
					if (((FSTInvariant) parentElement).getFullName().equals(i.getFullName())) {
						roleList.add(role);
						break;
					}
				}
			}

			return filter(roleList.toArray());
		} else if (parentElement instanceof FSTField) {
			// get all the roles that belong to a field
			final LinkedList<FSTRole> roleList = new LinkedList<FSTRole>();
			for (final FSTRole role : ((FSTField) parentElement).getRole().getFSTClass().getRoles()) {
				for (final FSTField f : role.getAllFields()) {
					if (f.getFullName().equals(((FSTField) parentElement).getFullName())) {
						roleList.add(role);
						break;
					}
				}
			}
			return filter(roleList.toArray());
		} else if (parentElement instanceof FSTDirective) {
			return ((FSTDirective) parentElement).getRoleElementChildren();
		} else if (parentElement instanceof FSTClassFragment) {
			final TreeSet<FSTMethod> methods = new TreeSet<FSTMethod>();
			final TreeSet<FSTField> fields = new TreeSet<FSTField>();
			final TreeSet<FSTClassFragment> innerClasses = new TreeSet<FSTClassFragment>();
			final TreeSet<FSTInvariant> invariants = new TreeSet<FSTInvariant>();

			final FSTClassFragment innerClassCast = (FSTClassFragment) parentElement;

			invariants.addAll(innerClassCast.getInvariants());
			final LinkedList<FSTClassFragment> allFragments = innerClassCast.getRole().getAllEqualFSTFragments(innerClassCast);
			for (final FSTClassFragment fstClassFragment : allFragments) {
				methods.addAll(fstClassFragment.getMethods());
				fields.addAll(fstClassFragment.getFields());
			}
			innerClasses.addAll(innerClassCast.getInnerClasses());

			obj = new IRoleElement[methods.size() + fields.size() + invariants.size() + innerClasses.size()];
			int pos = 0;
			System.arraycopy(invariants.toArray(), 0, obj, pos, invariants.size());
			System.arraycopy(fields.toArray(), 0, obj, pos += invariants.size(), fields.size());
			System.arraycopy(methods.toArray(), 0, obj, pos += fields.size(), methods.size());
			System.arraycopy(innerClasses.toArray(), 0, obj, pos += methods.size(), innerClasses.size());

		}

		return filter(obj);
	}

	@Override
	public Object getParent(Object element) {
		return null;
	}

	@Override
	public boolean hasChildren(Object element) {
		if (element instanceof FSTClass) {
			for (final FSTRole role : ((FSTClass) element).getRoles()) {
				if (!role.getClassFragment().getMethods().isEmpty() || !role.getClassFragment().getFields().isEmpty() || !role.getDirectives().isEmpty()
					|| !role.getInnerClasses().isEmpty()) {
					return true;
				}
			}
			return false;
		}

		if (element instanceof FSTMethod) {
			final FSTMethod fstMethod = (FSTMethod) element;
			final FSTRole role = fstMethod.getRole();
			return role.getMethods().contains(element) || !fstMethod.getFSTDirectives().isEmpty();
		}
		if (element instanceof FSTField) {
			return false;
		}

		if (element instanceof FSTInvariant) {
			return true;
		}

		if (element instanceof FSTDirective) {
			return ((FSTDirective) element).getRoleElementChildren().length != 0;
		}
		if (element instanceof FSTClassFragment) {
			final FSTClassFragment innerClass = (FSTClassFragment) element;
			if (!innerClass.getMethods().isEmpty() || !innerClass.getFields().isEmpty() || !innerClass.getInnerClasses().isEmpty()) {
				return true;
			}
		}

		return false;
	}

}
