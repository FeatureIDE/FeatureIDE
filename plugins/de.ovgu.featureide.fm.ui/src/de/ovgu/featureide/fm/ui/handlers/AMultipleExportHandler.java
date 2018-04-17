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
package de.ovgu.featureide.fm.ui.handlers;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Display;

import de.ovgu.featureide.fm.core.base.impl.FormatManager;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.handlers.base.AContainerHandler;
import de.ovgu.featureide.fm.ui.wizards.FormatConversionWizard;

public abstract class AMultipleExportHandler<T> extends AContainerHandler {

	private Path outputPath;
	private IPersistentFormat<T> outputFormat;

	@Override
	protected boolean startAction(IStructuredSelection selection) {
		if (super.startAction(selection)) {
			final FormatConversionWizard<T> wizard = new FormatConversionWizard<T>(getFormatManager());
			if (Window.OK == new WizardDialog(Display.getCurrent().getActiveShell(), wizard).open()) {
				try {
					outputPath = Paths.get(wizard.getOutputFolder());
					outputFormat = wizard.getOutputFormat();
					return ((outputPath != null) && (outputFormat != null));
				} catch (final Exception e) {
					FMUIPlugin.getDefault().logError(e);
				}
			}
		}
		return false;
	}

	@Override
	protected void singleAction(IContainer modelFolder) {
		final List<IFile> files = new ArrayList<>();
		try {
			modelFolder.accept(new IResourceVisitor() {
				@Override
				public boolean visit(IResource child) throws CoreException {
					if (child instanceof IFile) {
						files.add((IFile) child);
					}
					return true;
				}
			}, IResource.DEPTH_ONE, IResource.NONE);
			if (!files.isEmpty()) {
				for (final IFile file : files) {
					final Path modelFilePath = Paths.get(file.getLocationURI());
					String fileName = modelFilePath.getFileName().toString();
					final int extIndex = fileName.lastIndexOf('.');
					if (extIndex > 0) {
						fileName = fileName.substring(0, extIndex + 1) + outputFormat.getSuffix();
					}

					save(outputFormat, read(modelFilePath), outputPath.resolve(fileName));
				}
			}
		} catch (final CoreException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

	protected abstract FormatManager<? extends IPersistentFormat<T>> getFormatManager();

	protected abstract FileHandler<T> read(final Path modelFilePath);

	protected void save(final IPersistentFormat<T> format, FileHandler<T> fileHandler, final Path path) {
		if (!fileHandler.getLastProblems().containsError()) {
			FileHandler.save(path, fileHandler.getObject(), format);
		}
	}

}
