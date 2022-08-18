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
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import static de.ovgu.featureide.fm.core.localization.StringTable.IMPORT_FEATURE_MODEL;

import de.ovgu.featureide.fm.core.ExternalModelUtil;
import de.ovgu.featureide.fm.core.ExternalModelUtil.InvalidImportException;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

/**
 * Operation to import a feature model. Enables undo/redo functionality.
 *
 * @author Kevin Jedelhauser
 * @author Johannes Herschel
 */
public class ImportFeatureModelOperation extends AbstractFeatureModelOperation {

	/**
	 * The path of the model to be imported, relative either to the importing model or to its project.
	 */
	private final String relativePath;
	/**
	 * The alias to be used for the imported model. An empty string indicates no alias.
	 */
	private final String alias;

	/**
	 * The alias of the imported model, or its name if the alias is empty.
	 */
	private String importName;

	public ImportFeatureModelOperation(IFeatureModelManager featureModelManager, String relativePath, String alias) {
		super(featureModelManager, IMPORT_FEATURE_MODEL);
		this.relativePath = relativePath;
		this.alias = alias;
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		if (featureModel instanceof MultiFeatureModel) {
			final MultiFeatureModel multiFeatureModel = (MultiFeatureModel) featureModel;
			try {
				final MultiFeatureModel.UsedModel model = ExternalModelUtil.resolveImport(featureModel, relativePath, alias);
				importName = model.getVarName();
				multiFeatureModel.addExternalModel(model);
			} catch (final InvalidImportException e) {}
		}
		return FeatureIDEEvent.getDefault(EventType.IMPORTS_CHANGED);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		if (featureModel instanceof MultiFeatureModel) {
			final MultiFeatureModel multiFeatureModel = (MultiFeatureModel) featureModel;
			multiFeatureModel.removeExternalModel(importName);
		}
		return FeatureIDEEvent.getDefault(EventType.IMPORTS_CHANGED);
	}
}
