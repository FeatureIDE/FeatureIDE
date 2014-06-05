/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.featuremodel.commands;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.IUndoContext;
import org.eclipse.gef.commands.Command;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureRenamingOperation;

/**
 * Renames a currently selected feature.
 * 
 * @author Thomas Thuem
 */
public class FeatureRenamingCommand extends Command {
	
	private final FeatureModel featureModel;

	private final String oldName;
	
	private final String newName;

	public FeatureRenamingCommand(FeatureModel featureModel, String oldName, String newName) {
		super("Renaming feature " + oldName);
		this.featureModel = featureModel;
		this.oldName = oldName;
		this.newName = newName;
	}
	
	@Override
	public boolean canExecute() {
		if (newName == null)
			return false;
		if (featureModel.getFeatureNames().contains(newName))
			return false;
		return featureModel.getFMComposerExtension().isValidFeatureName(newName);
	}
	
	@Override
	public void execute() {
		FeatureRenamingOperation op = new FeatureRenamingOperation(featureModel, oldName, newName);
		op.addContext((IUndoContext) featureModel.getUndoContext());
		
		try {
			PlatformUI.getWorkbench().getOperationSupport()
					.getOperationHistory().execute(op, null, null);
		} catch (ExecutionException e) {
		FMUIPlugin.getDefault().logError(e);
			
		}
	}
	
}
