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

import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModelElement;
import de.ovgu.featureide.ui.ahead.GUIDefaults;


/**
 * This class is part of the outline. It maps the items
 * provided by the ContentProvider to visible items that
 * can be displayed inside a TreeView.
 * 
 * @author Tom Brosch
 */
public class JakLabelProvider implements ILabelProvider, GUIDefaults {
	
	public Image getImage(Object element) {
		if (element instanceof FSTModelElement) {
			FSTModelElement jakModelElement = (FSTModelElement)element;
			if (jakModelElement instanceof FSTField) {
				FSTField field = (FSTField)jakModelElement;
				if (field.isPrivate())
					return IMAGE_FIELD_PRIVATE;
				else if (field.isProtected())
					return IMAGE_FIELD_PROTECTED;
				else if (field.isPublic())
					return IMAGE_FIELD_PUBLIC;
				else 
					return IMAGE_FIELD_DEFAULT;
			} else if (jakModelElement instanceof FSTMethod) {
				FSTMethod method = (FSTMethod)jakModelElement;
				if (method.isPrivate())			
					return IMAGE_METHODE_PRIVATE;
				else if (method.isProtected())
					return IMAGE_METHODE_PROTECTED;
				else if (method.isPublic())
					return IMAGE_METHODE_PUBLIC;
				else 
					return IMAGE_METHODE_DEFAULT;
			} else if (jakModelElement instanceof FSTClass) {
				return IMAGE_CLASS;
			}
		}
		return null;
	}

	public String getText(Object element) {
		if( element instanceof FSTModelElement )
			return ((FSTModelElement)element).getName();
		
		return element.toString();
	}

	public void addListener(ILabelProviderListener listener) {
	}

	public void dispose() {
	}

	public boolean isLabelProperty(Object element, String property) {
		return false;
	}

	public void removeListener(ILabelProviderListener listener) {
	}
}
