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
package de.ovgu.featureide.fm.ui.editors.featuremodel.commands;

import static de.ovgu.featureide.fm.core.localization.StringTable.RENAMING_FEATURE;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.gef.commands.Command;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.FMComposerManager;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.RenameFeatureOperation;

/**
 * Renames a currently selected feature.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke
 */
public class FeatureRenamingCommand extends Command {

	private final IFeatureModel featureModel;

	private final String oldName;

	private final String newName;

	public FeatureRenamingCommand(IFeatureModel featureModel, String oldName, String newName) {
		super(RENAMING_FEATURE + oldName);
		this.featureModel = featureModel;
		this.oldName = oldName;
		this.newName = newName;
	}

	@Override
	public boolean canExecute() {
		if (newName == null) {
			return false;
		}
		if (Functional.toList(FeatureUtils.extractFeatureNames(featureModel.getFeatures())).contains(newName)) {
			return false;
		}

		if ((featureModel.getSourceFile() == null) || (featureModel.getSourceFile().toUri() == null)
			|| (ResourcesPlugin.getWorkspace().getRoot().findFilesForLocationURI(featureModel.getSourceFile().toUri())[0] == null)
			|| (FMComposerManager.getFMComposerExtension(
					ResourcesPlugin.getWorkspace().getRoot().findFilesForLocationURI(featureModel.getSourceFile().toUri())[0].getProject()) == null)) {
			return false;
		} else {
			return FMComposerManager
					.getFMComposerExtension(
							ResourcesPlugin.getWorkspace().getRoot().findFilesForLocationURI(featureModel.getSourceFile().toUri())[0].getProject())
					.isValidFeatureName(newName);
		}
	}

	@Override
	public void execute() {
		final RenameFeatureOperation op = new RenameFeatureOperation(featureModel, oldName, newName);

		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
		} catch (final ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);

		}
	}

}
