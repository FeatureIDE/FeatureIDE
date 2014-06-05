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
package de.ovgu.featureide.ahead.actions;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.SWT;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.ahead.AheadComposer;
import de.ovgu.featureide.core.IFeatureProject;

/**
 * 
 * A action to replace the composer of a given project.
 * 
 * @author Jens Meinicke
 */
public class ChangeComposerAction extends AbstractHandler {

	/**
	 * Calls the associated <code>ConversionAction</code> of the selected feature project.
	 */
	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		if (!openDialog()) return null;
		IFeatureProject featureProject = ComposerPropertyTester.getFeatureProject();
		if (AheadComposer.COMPOSER_ID.equals(featureProject.getComposerID())) {
			new AHEADToFeatureHouseConversion(featureProject);
		} else {
			new FeatureHouseToAHEADConversion(featureProject);
		}
		return null;
	}

	private boolean openDialog() {
		return MessageDialog.open(MessageDialog.WARNING, PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell(),
				"Composer Conversion", 
				"Source files will be changed automatically. FeatureHouse suppors Java 5 and AHEAD Java 4, this can cause problems during converion. You should have a copy of this project.",
				SWT.NONE);
		
				
				
	}
	

}
