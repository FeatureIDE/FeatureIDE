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
package de.ovgu.featureide.fm.ui.editors.featuremodel.commands;

import static de.ovgu.featureide.fm.core.localization.StringTable.RENAMING_FEATURE;

import java.net.URI;
import java.nio.file.Path;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.gef.commands.Command;

import de.ovgu.featureide.fm.core.FMComposerManager;
import de.ovgu.featureide.fm.core.IFMComposerExtension;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFileManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.RenameFeatureOperation;

/**
 * Renames a currently selected feature.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke
 */
public class FeatureRenamingCommand extends Command {

	private final IFeatureModelManager featureModelManager;

	private final String oldName;

	private final String newName;

	public FeatureRenamingCommand(IFeatureModelManager featureModelManager, String oldName, String newName) {
		super(RENAMING_FEATURE + oldName);
		this.featureModelManager = featureModelManager;
		this.oldName = oldName;
		this.newName = newName;
	}

	@Override
	public boolean canExecute() {
		if (newName == null) {
			return false;
		}
		final IFeatureModel featureModel = featureModelManager.getSnapshot();
		if (Functional.toList(FeatureUtils.extractFeatureNames(featureModel.getFeatures())).contains(newName)) {
			return false;
		}

		final Path sourcePath = featureModel.getSourceFile();
		if (sourcePath != null) {
			final URI sourceUri = sourcePath.toUri();
			if (sourceUri != null) {
				final IFile sourceFile = ResourcesPlugin.getWorkspace().getRoot().findFilesForLocationURI(sourceUri)[0];
				if (sourceFile != null) {
					final IFMComposerExtension fmComposerExtension = FMComposerManager.getFMComposerExtension(sourceFile.getProject());
					if (featureModelManager instanceof IFileManager) {
						final IPersistentFormat<?> format = ((IFileManager<?>) featureModelManager).getFormat();
						if ((format instanceof IFeatureModelFormat) && !((IFeatureModelFormat) format).isValidFeatureName(newName)) {
							return false;
						}
					}
					return (fmComposerExtension != null) && fmComposerExtension.isValidFeatureName(newName);
				}
			}
		}
		return false;
	}

	@Override
	public void execute() {
		FeatureModelOperationWrapper.run(new RenameFeatureOperation(featureModelManager, oldName, newName));
	}

}
