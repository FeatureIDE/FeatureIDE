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
package de.ovgu.featureide.fm.ui.views.outline;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.IColorProvider;
import org.eclipse.jface.viewers.IFontProvider;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.TreeItem;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.ProfileManager;
import de.ovgu.featureide.fm.core.ProfileManager.Project.Profile;
import de.ovgu.featureide.fm.core.annotation.ColorPalette;
import de.ovgu.featureide.fm.ui.PlugInProfileSerializer;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * This class is part of the outline. It maps the items provided by the
 * ContentProvider to visible items that can be displayed inside a TreeView.
 * 
 * @author Jan Wedding
 * @author Melanie Pflaume
 */
public class FmLabelProvider implements ILabelProvider, IFontProvider, GUIDefaults, IColorProvider {

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

	public void colorizeItems(TreeItem[] treeItems, IFile file) {

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
				return null; // TODO: Add here icon for feature model
			if (((Feature) element).getParent().isAlternative()) {
				return IMG_XOR;
			} else if (((Feature) element).getParent().isOr()) {
				return IMG_OR;
			} else if (((Feature) element).isMandatory()) {
				return IMG_MANDATORY;
			} else {
				return IMG_OPTIONAL;
			}
		} else if (element instanceof String) {
			return null; // TODO: Add here icon for "constraint" node
		} else if (element instanceof Constraint) {
			return null; // TODO: Add here icon for CONSTRAINT_ELEMENT node
		} else
			return null;
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

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.IFontProvider#getFont(java.lang.Object)
	 */
	@Override
	public Font getFont(Object element) {
		return DEFAULT_FONT;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.IColorProvider#getForeground(java.lang.Object)
	 */
	@Override
	public Color getForeground(Object element) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.IColorProvider#getBackground(java.lang.Object)
	 */

	/**
	 * @author Marcus Pinnecke
	 */
	//TODO: outsource method to global state
	private Profile getCurrentProfile(FeatureModel featureModel) {
		return ProfileManager.getProject(featureModel.xxxGetEclipseProjectPath(), PlugInProfileSerializer.FEATURE_PROJECT_SERIALIZER).getActiveProfile();
	}

	public Color getBackground(Object element) {
		Color col = null;

		if (element instanceof Feature) {

			Feature feature = (Feature) element;

			if (ProfileManager.toColorIndex(getCurrentProfile(feature.getFeatureModel()).getColor(feature.getName())) != -1) {
				col = new Color(null, ColorPalette.getRGB(
						ProfileManager.toColorIndex(getCurrentProfile(feature.getFeatureModel()).getColor(feature.getName())), 0.5f));
			}
		}
		return col;
	}
}
