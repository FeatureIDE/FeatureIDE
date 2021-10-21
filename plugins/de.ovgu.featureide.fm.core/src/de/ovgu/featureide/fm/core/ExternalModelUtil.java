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

	private ExternalModelUtil() {
		// Prevent instantiation
	}

	public static MultiFeatureModel.UsedModel resolveImport(Path importingPath, String importedPath, String alias) {
		final Path path = resolveImportPath(importingPath, importedPath);
		if (path == null) {
			return null;
		}

		final IFeatureModelManager importedFeatureModelManager = FeatureModelManager.getInstance(path);
		if (importedFeatureModelManager == null) {
			return null;
		}

		if (hasImportCycle(importingPath, importedFeatureModelManager.getVarObject())) {
			return null;
		}

		final int fileExtensionIndex = importedPath.lastIndexOf(".");
		if (fileExtensionIndex == -1) {
			return null;
		}

		final String modelName = importedPath.substring(0, fileExtensionIndex).replaceAll("[/\\\\]", ".");

		return new MultiFeatureModel.UsedModel(modelName, alias.isEmpty() ? modelName : alias, path, MultiFeature.TYPE_INSTANCE);
	}

	private static Path resolveImportPath(Path importingPath, String importedPath) {
		final IProject project = EclipseFileSystem.getResource(importingPath).getProject();
		final Path projectRelative = project.getFile(importedPath).getLocation().toFile().toPath();
		if (Files.exists(projectRelative)) {
			return projectRelative;
		} else {
			final Path modelRelative = importingPath.resolveSibling(importedPath);
			return Files.exists(modelRelative) ? modelRelative : null;
		}
	}

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
