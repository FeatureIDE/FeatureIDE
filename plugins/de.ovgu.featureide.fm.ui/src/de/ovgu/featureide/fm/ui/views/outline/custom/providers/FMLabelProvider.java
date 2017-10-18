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
package de.ovgu.featureide.fm.ui.views.outline.custom.providers;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.TreeItem;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.color.ColorPalette;
import de.ovgu.featureide.fm.core.color.FeatureColor;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineLabelProvider;
import de.ovgu.featureide.fm.ui.views.outline.standard.FmOutlineGroupStateStorage;

/**
 * This class is part of the outline. It maps the items provided by the ContentProvider to visible items that can be displayed inside a TreeView.
 *
 * @author Jan Wedding
 * @author Melanie Pflaume
 * @author Reimar Schroeter
 * @author Dominic Labsch
 * @author Daniel Psche
 * @author Christopher Sontag
 */
public class FMLabelProvider extends OutlineLabelProvider implements GUIDefaults {

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
	public void colorizeItems(TreeItem[] treeItems, IFile file) {

	}

	@Override
	public Image getImage(Object element) {
		if (element instanceof IFeature) {
			if ((((IFeature) element).getStructure().isRoot())) {
				return null; // TODO: Add here icon for feature model
			}
			if (((IFeature) element).getStructure().getParent().isAlternative()) {
				return IMG_XOR;
			} else if (((IFeature) element).getStructure().getParent().isOr()) {
				return IMG_OR;
			} else if (((IFeature) element).getStructure().isMandatory()) {
				return IMG_MANDATORY;
			} else {
				return IMG_OPTIONAL;
			}
		} else if (element instanceof String) {
			return null; // TODO: Add here icon for "constraint" node
		} else if (element instanceof IConstraint) {
			return null; // TODO: Add here icon for CONSTRAINT_ELEMENT node
		} else {
			return null;
		}
	}

	@Override
	public String getText(Object element) {
		if (element instanceof IFeature) {
			return ((IFeature) element).getName();
		} else if (element instanceof IConstraint) {
			return ((IConstraint) element).getNode().toString(NodeWriter.logicalSymbols);
		} else if (element instanceof FmOutlineGroupStateStorage) {
			return "";
		}

		return element.toString();
	}

	public Color getBackground(Object element) {
		Color col = null;

		if (element instanceof IFeature) {
			final IFeature feature = (IFeature) element;
			final FeatureColor color = FeatureColorManager.getColor(feature);
			if (color != FeatureColor.NO_COLOR) {
				col = new Color(null, ColorPalette.getRGB(color.getValue(), 0.5f));
			}
		}
		return col;
	}

	@Override
	public void init() {
		// TODO Auto-generated method stub

	}

	@Override
	public int getOutlineType() {
		return OUTLINE_FEATURE_MODEL;
	}

	@Override
	public void setForeground(TreeItem item, IFile file) {
		// TODO Auto-generated method stub

	}

	@Override
	public String getLabelProvName() {
		return "Feature Model Outline";
	}

	@Override
	public boolean refreshContent(IFile oldFile, IFile currentFile) {
		// TODO Auto-generated method stub
		return false;
	}

}
