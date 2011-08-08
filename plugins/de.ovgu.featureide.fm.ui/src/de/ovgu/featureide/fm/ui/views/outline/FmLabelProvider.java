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
package de.ovgu.featureide.fm.ui.views.outline;

import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Image;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * This class is part of the outline. It maps the items provided by the
 * ContentProvider to visible items that can be displayed inside a TreeView.
 * 
 * @author Jan Wedding
 * @author Melanie Pflaume
 */
public class FmLabelProvider implements ILabelProvider {


	private static Image IMG_OPTIONAL = FMUIPlugin.getImage("optional.gif");
	private static Image IMG_MANDATORY = FMUIPlugin.getImage("mandatory.gif");
	private static Image IMG_OR = FMUIPlugin.getImage("or.gif");
	private static Image IMG_XOR = FMUIPlugin.getImage("exor.gif");

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.jface.viewers.IBaseLabelProvider#addListener(org.eclipse.
	 * jface.viewers.ILabelProviderListener)
	 */
	@Override
	public void addListener(ILabelProviderListener listener) {
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.viewers.IBaseLabelProvider#dispose()
	 */
	@Override
	public void dispose() {
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.jface.viewers.IBaseLabelProvider#isLabelProperty(java.lang
	 * .Object, java.lang.String)
	 */
	@Override
	public boolean isLabelProperty(Object element, String property) {
		return false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.jface.viewers.IBaseLabelProvider#removeListener(org.eclipse
	 * .jface.viewers.ILabelProviderListener)
	 */
	@Override
	public void removeListener(ILabelProviderListener listener) {
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.viewers.ILabelProvider#getImage(java.lang.Object)
	 */
	@Override
	public Image getImage(Object element) {
		if (element instanceof Feature) {
			if ((((Feature) element).isRoot()))
				return null;
			if (((Feature) element).getParent().isAlternative() ||((Feature) element).getParent().isOr())
				return null;
			if (((Feature) element).isMandatory()) {
				//gc.drawImage(IMG_MANDATORY, 0, 0);
				return IMG_MANDATORY;
			} else {
				//gc.drawImage(IMG_OPTIONAL, 0, 0);
				return IMG_OPTIONAL;
			}
		} else if (element instanceof FmOutlineGroupStateStorage) {
			if (((FmOutlineGroupStateStorage)element).isOrGroup()) {
				return IMG_OR;
			} else {
				return IMG_XOR;
			}
		} else {
			return null;
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.viewers.ILabelProvider#getText(java.lang.Object)
	 */
	@Override
	public String getText(Object element) {
		if (element instanceof Feature)
			return ((Feature) element).getName();
		else if (element instanceof Constraint)
			return ((Constraint) element).getNode().toString(NodeWriter.logicalSymbols);
		else if (element instanceof FmOutlineGroupStateStorage)
			return "";
	
		return element.toString();
	}
}