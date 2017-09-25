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
package de.ovgu.featureide.fm.ui.views.outline.custom.providers;

import static de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.NO_DATA_TO_DISPLAY_AVAILABLE_;

import java.nio.file.Paths;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.Viewer;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineTreeContentProvider;
import de.ovgu.featureide.fm.ui.views.outline.standard.FmOutlineGroupStateStorage;

/**
 * This class is part of the outline. It provides the content that should be displayed. Therefore it maps the information provided by the fmProject to the
 * methods of the ITreeContentProvider interface.
 *
 * @author Jan Wedding
 * @author Melanie Pflaume
 * @author Marcus Pinnecke
 */
public class FMTreeContentProvider extends OutlineTreeContentProvider {

	private IFeatureModel fModel;

	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		if (newInput != null) {
			if (newInput instanceof IFeatureModel) {
				fModel = ((IFeatureModel) newInput);
			} else if (newInput instanceof IFile) {
				if (((IFile) newInput).exists()) {
					final FeatureModelManager fmm = FeatureModelManager.getInstance(Paths.get(((IFile) newInput).getLocationURI()));
					if (fmm != null) {
						fModel = fmm.getObject();
					}
				}
			}
		}

	}

	public IFeatureModel getFeatureModel() {
		return fModel;
	}

	@Override
	public Object[] getElements(Object inputElement) {
		Object[] elements;
		if ((fModel != null) && (fModel.getStructure().getRoot() != null)) {
			elements = new Object[2];
			elements[0] = fModel.getStructure().getRoot().getFeature();
			elements[1] = CONSTRAINTS;
			return elements;
		}

		return new String[] { NO_DATA_TO_DISPLAY_AVAILABLE_ };
	}

	@Override
	public Object[] getChildren(Object parentElement) {
		if (parentElement == null) {
			return null;
		}

		// we have a String as parent of constraints
		if ((parentElement instanceof String) && CONSTRAINTS.equals(parentElement)) {
			final Object[] elements = new Object[fModel.getConstraintCount()];
			final List<IConstraint> cList = fModel.getConstraints();
			for (int i = 0; i < fModel.getConstraintCount(); i++) {
				elements[i] = cList.get(i);
			}
			return elements;
		}

		// we store the group stage into an extra object in order to be able to
		// show an own element for GroupStages
		if (parentElement instanceof FmOutlineGroupStateStorage) {

			return featureListToArray(
					FeatureUtils.convertToFeatureList(((FmOutlineGroupStateStorage) parentElement).getFeature().getStructure().getChildren()));
		}

		if (!(parentElement instanceof IFeature)) {
			return null;
		}
		if (!((IFeature) parentElement).getStructure().hasChildren()) {
			return null;
		}

		return featureListToArray(FeatureUtils.convertToFeatureList(((IFeature) parentElement).getStructure().getChildren()));
	}

	/**
	 * converts a list of Features into an Array
	 *
	 * @param f FeatureList
	 * @return Array of Features
	 */
	private IFeature[] featureListToArray(List<IFeature> f) {
		final IFeature[] fArray = new IFeature[f.size()];
		for (int i = 0; i < f.size(); i++) {
			fArray[i] = f.get(i);
		}
		return fArray;
	}

	@Override
	public Object getParent(Object element) {
		if (element instanceof IFeature) {
			return ((IFeature) element).getStructure().getParent();
		} else if (element instanceof IConstraint) {
			return CONSTRAINTS;
		} else if (element instanceof FmOutlineGroupStateStorage) {
			return ((FmOutlineGroupStateStorage) element).getFeature();
		}

		return null;
	}

	@Override
	public boolean hasChildren(Object element) {
		if (element instanceof IFeature) {
			return ((IFeature) element).getStructure().hasChildren();
		} else if (element instanceof FmOutlineGroupStateStorage) {
			return true;
		} else if (element instanceof String) {
			if (CONSTRAINTS.equals(element)) {
				return fModel.getConstraintCount() > 0;
			}
		}

		return false;
	}

	/*
	 * FIX for Bug #582
	 */
	@Override
	public void dispose() {}

}
