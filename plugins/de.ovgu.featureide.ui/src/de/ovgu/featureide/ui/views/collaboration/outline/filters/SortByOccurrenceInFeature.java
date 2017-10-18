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
package de.ovgu.featureide.ui.views.collaboration.outline.filters;

import java.util.Arrays;
import java.util.Comparator;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.resource.ImageDescriptor;

import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTInvariant;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.fstmodel.IRoleElement;
import de.ovgu.featureide.core.fstmodel.RoleElement;
import de.ovgu.featureide.fm.ui.views.outline.custom.filters.IOutlineFilter;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * Filter to sort the entries in the collaboration outline by their orrurence in the file.
 *
 * @author Dominic Labsch
 * @author Daniel P�sche
 */
public class SortByOccurrenceInFeature implements IOutlineFilter {

	private IFile file;
	private boolean enabled = false;

	public IFile getFile() {
		return file;
	}

	public void setFile(IFile file) {
		this.file = file;
	}

	@Override
	public Object[] filter(Object[] obj) {
		if ((obj.length > 0) && (obj[0] instanceof RoleElement)) {
			Arrays.sort(obj, new Comparator<Object>() {

				@Override
				public int compare(Object o1, Object o2) {
					final boolean c1 = isNotInCurrentFeature((IRoleElement) o1);
					final boolean c2 = isNotInCurrentFeature((IRoleElement) o2);
					if (c1 != c2) {
						return c1 ? 1 : -1;
					}
					return 0;
				}
			});
		}
		return obj;
	}

	// check if element is in the current feature
	public boolean isNotInCurrentFeature(IRoleElement element) {
		for (final FSTRole role : element.getRole().getFSTClass().getRoles()) {
			if (role.getFile().equals(file) && (((element instanceof FSTMethod) && role.getAllMethods().contains(element))
				|| ((element instanceof FSTInvariant) && role.getClassFragment().getInvariants().contains(element))
				|| ((element instanceof FSTField) && role.getAllFields().contains(element))
				|| ((element instanceof FSTClassFragment) && role.getAllInnerClasses().contains(element)))) {

				return false;
			}
		}
		return true;
	}

	public boolean isEnabled() {
		return enabled;
	}

	public void setEnabled(boolean enabled) {
		this.enabled = enabled;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.filters.IOutlineFilter#getName()
	 */
	@Override
	public String getName() {
		return "Sort By Occurence In Feature";
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.filters.IOutlineFilter#getImage()
	 */
	@Override
	public ImageDescriptor getImage() {
		return UIPlugin.getDefault().getImageDescriptor("icons/alphab_sort_co.gif");
	}
}
