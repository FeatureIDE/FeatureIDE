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

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModelElement;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;
import de.ovgu.featureide.ui.views.collaboration.model.Class;
import de.ovgu.featureide.ui.views.collaboration.model.Role;

/**
 * provides labels and images for Collaboration outline
 * 
 * @author Jan Wedding
 * @author Melanie Pflaume
 */
public class CollaborationOutlineLabelProvider implements ILabelProvider,GUIDefaults{

	private IFile file;

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.IBaseLabelProvider#addListener(org.eclipse.jface.viewers.ILabelProviderListener)
	 */
	@Override
	public void addListener(ILabelProviderListener listener) {
		
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.IBaseLabelProvider#dispose()
	 */
	@Override
	public void dispose() {

	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.IBaseLabelProvider#isLabelProperty(java.lang.Object, java.lang.String)
	 */
	@Override
	public boolean isLabelProperty(Object element, String property) {
		return false;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.IBaseLabelProvider#removeListener(org.eclipse.jface.viewers.ILabelProviderListener)
	 */
	@Override
	public void removeListener(ILabelProviderListener listener) {
	
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ILabelProvider#getImage(java.lang.Object)
	 */
	@Override
	public Image getImage(Object element) {
		if (element instanceof FSTModelElement) {
			FSTModelElement fstModelElement = (FSTModelElement)element;
			if (fstModelElement instanceof FSTField) {
				FSTField field = (FSTField)fstModelElement;
				if (field.isPrivate())
					return IMAGE_FIELD_PRIVATE;
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
		} else if (element instanceof Class) {
			return IMAGE_CLASS;
		}
		return null;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ILabelProvider#getText(java.lang.Object)
	 */
	@Override
	public String getText(Object element) {
		if (element instanceof  Class) {
			String toAppend = ""; 
			for (Role r : ((Class)element).getRoles()) {
				if (r.directives.size() > 0) {
					return  ((Class)element).getName();
				}
				if (r.getRoleFile().equals(file)) {
					toAppend = " - " + r.featureName;
				}
			}
			return  ((Class)element).getName()+toAppend;
		}
		
		if (element instanceof FSTMethod)
			return ((FSTMethod)element).getName();
		
		if (element instanceof FSTField)
			return ((FSTField)element).getName();
		
		if (element instanceof FSTFeature)
			return ((FSTFeature)element).getName();
		
		if (element instanceof Role)
			return ((Role)element).featureName;
		
		if (element instanceof FSTDirective) {
			return ((FSTDirective)element).toString();
		}
		
		if (element instanceof String)
			return (String) element;
		
		return "";
	}

	/**
	 * @param iFile
	 */
	public void setFile(IFile iFile) {
		this.file = iFile;
	}

}
