/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.featurehouse.refactoring.pullUp;

import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractFieldSignature;
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
//import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.base.impl.Feature;
import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;

/**
 * Provides labels and images for Refactoring PullUp Hierarchy
 * 
 * @author Steffen Schulze
 */
public class PullUpHierarchyLabelProvider implements ILabelProvider {

	@Override
	public void addListener(ILabelProviderListener listener) {}

	@Override
	public void dispose() {}

	@Override
	public boolean isLabelProperty(Object element, String property) {
		return false;
	}

	@Override
	public void removeListener(ILabelProviderListener listener) {}

	@Override
	public Image getImage(Object element) {
		if (element instanceof Feature) {
			return GUIDefaults.IMAGE_FEATURE;
		} else if (element instanceof ExtendedPullUpSignature) {
			AbstractSignature extendSignature = ((ExtendedPullUpSignature) element).getSignature();
			if (extendSignature instanceof AbstractMethodSignature) {
				switch (((AbstractMethodSignature) extendSignature).getVisibilty()) {
				case AbstractSignature.VISIBILITY_DEFAULT:
					return GUIDefaults.IMAGE_METHODE_DEFAULT;
				case AbstractSignature.VISIBILITY_PRIVATE:
					return GUIDefaults.IMAGE_METHODE_PRIVATE;
				case AbstractSignature.VISIBILITY_PROTECTED:
					return GUIDefaults.IMAGE_METHODE_PROTECTED;
				case AbstractSignature.VISIBILITY_PUBLIC:
					return GUIDefaults.IMAGE_METHODE_PUBLIC;
				}
			} else if (extendSignature instanceof AbstractFieldSignature) {
				switch (((AbstractFieldSignature) extendSignature).getVisibilty()) {
				case AbstractSignature.VISIBILITY_DEFAULT:
					return GUIDefaults.IMAGE_FIELD_DEFAULT;
				case AbstractSignature.VISIBILITY_PRIVATE:
					return GUIDefaults.IMAGE_FIELD_PRIVATE;
				case AbstractSignature.VISIBILITY_PROTECTED:
					return GUIDefaults.IMAGE_FIELD_PROTECTED;
				case AbstractSignature.VISIBILITY_PUBLIC:
					return GUIDefaults.IMAGE_FIELD_PUBLIC;
				}
			} else if (extendSignature instanceof AbstractClassSignature) {
				return GUIDefaults.IMAGE_CLASS;
			}
		}

		return null;
	}

	@Override
	public String getText(Object element) {
		if (element instanceof Feature) {
			return ((Feature) element).getDisplayName();
		} else if (element instanceof ExtendedPullUpSignature) {
			AbstractSignature extendSignature = ((ExtendedPullUpSignature) element).getSignature();
			if (extendSignature instanceof AbstractMethodSignature) {
				final AbstractMethodSignature method = (AbstractMethodSignature) extendSignature;
				final StringBuilder sb = new StringBuilder();
				sb.append(method.getName());
				sb.append('(');
				for (String parameterType : method.getParameterTypes()) {
					sb.append(parameterType);
					sb.append(", ");
				}
				if (method.getParameterTypes().size() > 0) {
					sb.delete(sb.length() - 2, sb.length());
				}
				sb.append(')');
				if (!method.isConstructor()) {
					sb.append(" : ");
					sb.append(method.getType());
				}
				return sb.toString();
			} else if (extendSignature instanceof AbstractFieldSignature) {
				final AbstractFieldSignature field = (AbstractFieldSignature) extendSignature;
				return field.getName() + " : " + field.getType();
			} else if (extendSignature instanceof AbstractClassSignature) {
				return ((AbstractClassSignature) extendSignature).getName();
			}
		}
		return element.toString();
	}

}
