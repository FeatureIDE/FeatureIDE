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
package de.ovgu.featureide.fm.ui.handlers;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Display;

import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.handlers.base.ASelectionHandler;
import de.ovgu.featureide.fm.ui.handlers.base.SelectionWrapper;
import de.ovgu.featureide.fm.ui.wizards.FeatureModelConversionWizard;

/**
 * 
 * @author Sebastian Krieter
 */
public class FeatureModelConversionHandler extends ASelectionHandler {

	@Override
	protected boolean startAction(IStructuredSelection selection) {
		final IContainer next = SelectionWrapper.init(selection, IContainer.class).getNext();
		if (next != null) {
			final FeatureModelConversionWizard wizard = new FeatureModelConversionWizard();
			wizard.init(null, selection);
			final WizardDialog dialog = new WizardDialog(Display.getCurrent().getActiveShell(), wizard);
			if (dialog.open() == Dialog.OK) {
				final IFeatureModelFormat inputFormat = wizard.getInputFormat();
				final IFeatureModelFormat outputFormat = wizard.getOutputFormat();
				if (inputFormat == null || outputFormat == null) {
					return false;
				}
				final Path projectPath = Paths.get(next.getProject().getLocationURI());
				final Path outputPath = projectPath.resolve(wizard.getOutputFolder());
				
				try {
					if (!Files.exists(outputPath)) {
						Files.createDirectory(outputPath);
					}
					final IResource[] members = next.members();
					for (IResource resource : members) {
						if (resource instanceof IFile && resource.isAccessible()) {
							try {
								final IFeatureModel fm = FMFactoryManager.getFactory(inputFormat).createFeatureModel();
								String name = resource.getName();
								final int lastIndexOf = name.lastIndexOf('.');
								if (lastIndexOf > 0) {
									name = name.substring(0, lastIndexOf);
								}
								FileHandler.convert(Paths.get(resource.getLocationURI()),
										outputPath.resolve(name + "." + outputFormat.getSuffix()), fm, inputFormat,
										outputFormat);
							} catch (NoSuchExtensionException e) {
								FMUIPlugin.getDefault().logError(e);
							}
						}
					}
				} catch (CoreException | IOException e) {
					FMUIPlugin.getDefault().logError(e);
				}

			}
		}
		return true;
	}

	@Override
	protected void singleAction(Object element) {

	}

	@Override
	protected void endAction() {
		super.endAction();
	}

}
