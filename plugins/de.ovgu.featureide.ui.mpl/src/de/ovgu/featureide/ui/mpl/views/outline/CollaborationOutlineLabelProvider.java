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
package de.ovgu.featureide.ui.mpl.views.outline;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.fstmodel.RoleElement;
//import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;

/**
 * Provides labels and images for Collaboration outline
 * 
 * @author Jan Wedding
 * @author Melanie Pflaume
 */
public class CollaborationOutlineLabelProvider implements ILabelProvider,GUIDefaults{

	private IFile file;

	@Override
	public void addListener(ILabelProviderListener listener) {
		
	}

	@Override
	public void dispose() {

	}

	@Override
	public boolean isLabelProperty(Object element, String property) {
		return false;
	}

	@Override
	public void removeListener(ILabelProviderListener listener) {
	
	}

	@Override
	public Image getImage(Object element) {
		if (element instanceof RoleElement) {
			RoleElement fstModelElement = (RoleElement)element;
			if (fstModelElement instanceof FSTField) {
				FSTField field = (FSTField)fstModelElement;
				if (field.isPrivate())
					return GUIDefaults.IMAGE_FIELD_PRIVATE;
				else if (field.isProtected())
					return IMAGE_FIELD_PROTECTED;
				else if (field.isPublic())
					return IMAGE_FIELD_PUBLIC;
				else 
					return IMAGE_FIELD_DEFAULT;
			} else if (fstModelElement instanceof FSTMethod) {
				FSTMethod method = (FSTMethod)fstModelElement;
				if (method.isPrivate())			
					return IMAGE_METHODE_PRIVATE;
				else if (method.isProtected())
					return IMAGE_METHODE_PROTECTED;
				else if (method.isPublic())
					return IMAGE_METHODE_PUBLIC;
				else 
					return IMAGE_METHODE_DEFAULT;
			}
		} else if (element instanceof FSTClass) {
			return IMAGE_CLASS;
		}
		return null;
	}

	@Override
	public String getText(Object element) {
		if (element instanceof  FSTClass) {
			String toAppend = ""; 
			for (FSTRole r : ((FSTClass)element).getRoles()) {
				if (!r.getDirectives().isEmpty()) {
					return  ((FSTClass)element).getName();
				}
				if (r.getFile().equals(file)) {
					toAppend = " - " + r.getFeature().getName();
				}
			}
			return  ((FSTClass)element).getName()+toAppend;
		}
		
		if (element instanceof FSTMethod)
			return ((FSTMethod)element).getFullName();
		
		if (element instanceof FSTField)
			return ((FSTField)element).getFullName();
		
		if (element instanceof FSTFeature)
			return ((FSTFeature)element).getName();
		
		if (element instanceof FSTRole)
			return ((FSTRole)element).getFeature().getName();
		
		if (element instanceof FSTDirective) {
			return ((FSTDirective)element).toString();
		}
		
		if (element instanceof String)
			return (String) element;
		
		return "";
	}

	public void setFile(IFile file) {
		this.file = file;
	}

}
