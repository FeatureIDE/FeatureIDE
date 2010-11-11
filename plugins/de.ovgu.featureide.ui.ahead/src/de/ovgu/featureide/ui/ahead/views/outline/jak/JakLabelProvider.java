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

import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.core.fstmodel.IClass;
import de.ovgu.featureide.core.fstmodel.IFSTModelElement;
import de.ovgu.featureide.core.fstmodel.IField;
import de.ovgu.featureide.core.fstmodel.IMethod;
import de.ovgu.featureide.ui.ahead.AheadUIPlugin;


/**
 * This class is part of the outline. It maps the items
 * provided by the ContentProvider to visible items that
 * can be displayed inside a TreeView.
 * 
 * @author Tom Brosch
 */
public class JakLabelProvider implements ILabelProvider {
	
	private static Image IMAGE_FIELD_PRIVATE = AheadUIPlugin.getImage("field_private_obj.gif");
	private static Image IMAGE_FIELD_PROTECTED = AheadUIPlugin.getImage("field_protected_obj.gif");
	private static Image IMAGE_FIELD_PUBLIC = AheadUIPlugin.getImage("field_public_obj.gif");
	private static Image IMAGE_FIELD_DEFAULT = AheadUIPlugin.getImage("field_default_obj.gif");
	private static Image IMAGE_METHODE_PRIVATE = AheadUIPlugin.getImage("private_co.gif");
	private static Image IMAGE_METHODE_PROTECTED = AheadUIPlugin.getImage("/protected_co.gif");
	private static Image IMAGE_METHODE_PUBLIC = AheadUIPlugin.getImage("public_co.gif");
	private static Image IMAGE_METHODE_DEFAULT =  AheadUIPlugin.getImage("default_co.gif");
	private static Image IMAGE_CLASS = AheadUIPlugin.getImage("class_obj.gif");
	
	public Image getImage(Object element) {
		if (element instanceof IFSTModelElement) {
			IFSTModelElement jakModelElement = (IFSTModelElement)element;
			if (jakModelElement instanceof IField) {
				IField field = (IField)jakModelElement;
				if (field.isPrivate())
					return IMAGE_FIELD_PRIVATE;
				else if (field.isProtected())
					return IMAGE_FIELD_PROTECTED;
				else if (field.isPublic())
					return IMAGE_FIELD_PUBLIC;
				else 
					return IMAGE_FIELD_DEFAULT;
			} else if (jakModelElement instanceof IMethod) {
				IMethod method = (IMethod)jakModelElement;
				if (method.isPrivate())			
					return IMAGE_METHODE_PRIVATE;
				else if (method.isProtected())
					return IMAGE_METHODE_PROTECTED;
				else if (method.isPublic())
					return IMAGE_METHODE_PUBLIC;
				else 
					return IMAGE_METHODE_DEFAULT;
			} else if (jakModelElement instanceof IClass) {
				return IMAGE_CLASS;
			}
		}
		return null;
	}

	public String getText(Object element) {
		if( element instanceof IFSTModelElement )
			return ((IFSTModelElement)element).getName();
		
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
