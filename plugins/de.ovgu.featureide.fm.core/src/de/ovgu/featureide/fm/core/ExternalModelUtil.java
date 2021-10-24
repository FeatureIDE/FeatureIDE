/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2020  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core;

import static de.ovgu.featureide.fm.core.localization.StringTable.IMPORT_FEATURE_MODEL_ERROR_IMPORT_CYCLE;
import static de.ovgu.featureide.fm.core.localization.StringTable.IMPORT_FEATURE_MODEL_ERROR_NAME_ALREADY_EXISTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.IMPORT_FEATURE_MODEL_ERROR_NONEXISTENT_PATH;
import static de.ovgu.featureide.fm.core.localization.StringTable.IMPORT_FEATURE_MODEL_ERROR_NOT_A_FEATURE_MODEL;

import java.nio.file.Files;
import java.nio.file.Path;

import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.MultiFeature;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.io.EclipseFileSystem;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

/**
 * Utility methods for dealing with external models of {@link MultiFeatureModel MultiFeatureModels}.
 *
 * @author Kevin Jedelhauser
 * @author Johannes Herschel
 */
public final class ExternalModelUtil {

	/**
	 * Exception type thrown if an import is invalid to provide information about the reason why the import is invalid.
	 *
	 * @author Kevin Jedelhauser
	 * @author Johannes Herschel
	 */
	public static class InvalidImportException extends Exception {

		private static final long serialVersionUID = 4910781280930873985L;

		public InvalidImportException(String message) {
			super(message);
		}
	}

	private ExternalModelUtil() {
		// Prevent instantiation
	}

	/**
	 * Resolves and validates the import path <code>importedPath</code> for an external feature model of the feature model <code>importingModel</code>. The
	 * import path must be either relative to the importing model or to its project.
	 *
	 * The import is valid if <ul><li>the import path exists,</li> <li>it represents a feature model file,</li> <li>the feature model represented by the import
	 * path does not import the importing model, so importing it will not create a cyclic import, and</li> <li>the importing model does not already have an
	 * import with the same alias, or model name if the alias is empty.</li></ul>
	 *
	 * @param importingModel The importing feature model.
	 * @param importedPath The path of the model to be imported.
	 * @param alias The alias to use for the model to be imported. If it is the empty string, the alias will be the same as the model name.
	 * @return A {@link MultiFeatureModel.UsedModel} representing the model to be imported.
	 * @throws InvalidImportException If the import is invalid. Contains a message describing the reason why the import is invalid.
	 */
	public static MultiFeatureModel.UsedModel resolveImport(IFeatureModel importingModel, String importedPath, String alias) throws InvalidImportException {
		final Path importingPath = importingModel.getSourceFile();

		// Check that import path exists
		final Path path = resolveImportPath(importingPath, importedPath);
		if (path == null) {
			throw new InvalidImportException(IMPORT_FEATURE_MODEL_ERROR_NONEXISTENT_PATH);
		}

		// Check that import path refers to a feature model file
		final IFeatureModelManager importedFeatureModelManager = FeatureModelManager.getInstance(path);
		if (importedFeatureModelManager == null) {
			throw new InvalidImportException(IMPORT_FEATURE_MODEL_ERROR_NOT_A_FEATURE_MODEL);
		}

		// Check for cyclic imports
		if (hasImportCycle(importingPath, importedFeatureModelManager.getVarObject())) {
			throw new InvalidImportException(IMPORT_FEATURE_MODEL_ERROR_IMPORT_CYCLE);
		}

		// Check that import path can be converted to model name
		final int fileExtensionIndex = importedPath.lastIndexOf(".");
		if (fileExtensionIndex == -1) {
			throw new InvalidImportException(IMPORT_FEATURE_MODEL_ERROR_NOT_A_FEATURE_MODEL);
		}

		// Determine name and alias
		// Remove file extension and replace / and \ by .
		final String modelName = importedPath.substring(0, fileExtensionIndex).replaceAll("[/\\\\]", ".");
		// Use model name as alias if alias is empty
		final String modelAlias = alias.isEmpty() ? modelName : alias;

		// Check that name is unique
		if ((importingModel instanceof MultiFeatureModel) && (((MultiFeatureModel) importingModel).getExternalModel(modelAlias) != null)) {
			throw new InvalidImportException(IMPORT_FEATURE_MODEL_ERROR_NAME_ALREADY_EXISTS);
		}

		return new MultiFeatureModel.UsedModel(modelName, modelAlias, path, MultiFeature.TYPE_INSTANCE);
	}

	/**
	 * Resolves the import path <code>importedPath</code> for an external model of the feature model at <code>importingPath</code>. The import path is first
	 * considered relative to the importing model's project. If this path does not exist, the import path is considered relative to the importing model itself.
	 *
	 * @param importingPath The path of the importing feature model
	 * @param importedPath The path of an external model to be imported
	 * @return A {@link Path} representing the resolved path, or null if the path could not be resolved
	 */
	private static Path resolveImportPath(Path importingPath, String importedPath) {
		if (importedPath.equals("")) {
			// Return if path is empty, as getFile will throw an exception if called with an empty path
			return null;
		}
		final IProject project = EclipseFileSystem.getResource(importingPath).getProject();
		final Path projectRelative = project.getFile(importedPath).getLocation().toFile().toPath();
		if (Files.exists(projectRelative)) {
			return projectRelative;
		} else {
			final Path modelRelative = importingPath.resolveSibling(importedPath);
			return Files.exists(modelRelative) ? modelRelative : null;
		}
	}

	/**
	 * Checks for a cycle of imported models that would be created by importing <code>importedModel</code> into the model at <code>importingPath</code> by
	 * testing whether <code>importedModel</code> imports the model at <code>importingPath</code> (possibly indirectly).
	 *
	 * @param importingPath The path of the importing feature model
	 * @param importedModel A feature model to be imported, which is tested for an import of the importing model
	 * @return True if <code>importedModel</code> imports the model at <code>importingPath</code> (possibly indirectly), or if they are the same. False
	 *         otherwise.
	 */
	private static boolean hasImportCycle(Path importingPath, IFeatureModel importedModel) {
		if (importingPath.equals(importedModel.getSourceFile())) {
			return true;
		}
		if (!(importedModel instanceof MultiFeatureModel)) {
			return false;
		}
		for (final MultiFeatureModel.UsedModel usedModel : ((MultiFeatureModel) importedModel).getExternalModels().values()) {
			final IFeatureModelManager importedManager = FeatureModelManager.getInstance(usedModel.getPath());
			if (importedManager != null) {
				if (hasImportCycle(importingPath, importedManager.getVarObject())) {
					return true;
				}
			} else {
				return false;
			}
		}
		return false;
	}
}
