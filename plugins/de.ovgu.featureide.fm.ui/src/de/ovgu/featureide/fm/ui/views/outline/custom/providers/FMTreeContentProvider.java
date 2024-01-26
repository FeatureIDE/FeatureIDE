/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
import static de.ovgu.featureide.fm.core.localization.StringTable.OUTLINE_IMPORTS;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.Viewer;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.io.EclipseFileSystem;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IManager;
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

	private IManager<IFeatureModel> featureModelManager;

	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		if (newInput != null) {
			if (newInput instanceof FeatureModelManager) {
				featureModelManager = ((FeatureModelManager) newInput);
			} else if (newInput instanceof IFile) {
				if (((IFile) newInput).exists()) {
					final Path path = EclipseFileSystem.getPath(((IFile) newInput));
					if (FeatureModelManager.isFileSupported(path)) {
						final FeatureModelManager fmm = FeatureModelManager.getInstance(path);
						if (fmm != null) {
							featureModelManager = fmm;
						}
					}
				}
			}
		}

	}

	@Override
	public Object[] getElements(Object inputElement) {
		if (featureModelManager != null) {
			final IFeatureModel fModel = featureModelManager.getSnapshot();
			if ((fModel != null) && (fModel.getStructure().getRoot() != null)) {
				final List<Object> elements = new ArrayList<>();
				elements.add(fModel.getStructure().getRoot().getFeature());
				elements.add(CONSTRAINTS);
				if (fModel instanceof MultiFeatureModel) {
					elements.add(OUTLINE_IMPORTS);
				}
				return elements.toArray();
			}
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
			final IFeatureModel fModel = featureModelManager.getSnapshot();
			final Object[] elements = new Object[fModel.getConstraintCount()];
			final List<IConstraint> cList = fModel.getConstraints();
			for (int i = 0; i < fModel.getConstraintCount(); i++) {
				elements[i] = cList.get(i);
			}
			return elements;
		}

		if ((parentElement instanceof String) && OUTLINE_IMPORTS.equals(parentElement)) {
			final IFeatureModel fModel = featureModelManager.getSnapshot();
			if (fModel instanceof MultiFeatureModel) {
				return ((MultiFeatureModel) fModel).getExternalModels().values().toArray();
			}
			return null;
		}

		// we store the group stage into an extra object in order to be able to
		// show an own element for GroupStages
		if (parentElement instanceof FmOutlineGroupStateStorage) {

			return featureListToArray(
					FeatureUtils.convertToFeatureList(((FmOutlineGroupStateStorage) parentElement).getFeature().getStructure().getChildren()));
		}

		if (!(parentElement instanceof IFeature) || !((IFeature) parentElement).getStructure().hasChildren()) {
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
		} else if (element instanceof MultiFeatureModel.UsedModel) {
			return OUTLINE_IMPORTS;
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
		} else if ((element instanceof String) && CONSTRAINTS.equals(element)) {
			return featureModelManager.getSnapshot().getConstraintCount() > 0;
		} else if ((element instanceof String) && OUTLINE_IMPORTS.equals(element)) {
			final IFeatureModel fModel = featureModelManager.getSnapshot();
			return (fModel instanceof MultiFeatureModel) && !((MultiFeatureModel) fModel).getExternalModels().isEmpty();
		}

		return false;
	}

	/*
	 * FIX for Bug #582
	 */
	@Override
	public void dispose() {}

}
