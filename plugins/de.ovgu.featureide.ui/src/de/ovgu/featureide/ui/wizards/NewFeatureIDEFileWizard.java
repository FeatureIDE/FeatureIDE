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
package de.ovgu.featureide.ui.wizards;

import static de.ovgu.featureide.fm.core.localization.StringTable.CREATING;
import static de.ovgu.featureide.fm.core.localization.StringTable.NEW_FEATUREIDE_SOURCE_FILE;
import static de.ovgu.featureide.fm.core.localization.StringTable.OPENING_FILE_FOR_EDITING___;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.lang.reflect.InvocationTargetException;
import java.nio.charset.Charset;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWizard;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;

import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * A wizard to create a new language specific featureIDE file.
 *
 * @author Dariusz Krolikowski
 */
public class NewFeatureIDEFileWizard extends Wizard implements INewWizard {

	public static final String ID = UIPlugin.PLUGIN_ID + ".wizards.NewFeatureIDEFileWizard";

	public NewFeatureIDEFilePage page;

	private ISelection selection;

	private String feature;

	private String clss;

	private String pack;

	/**
	 * Constructor for NewFeatureIDEFileWizard.
	 */
	public NewFeatureIDEFileWizard() {
		super();
		setNeedsProgressMonitor(true);
		setWindowTitle(NEW_FEATUREIDE_SOURCE_FILE);
	}

	/**
	 * Adding the page to the wizard.
	 */
	@Override
	public void addPages() {
		page = new NewFeatureIDEFilePage(selection, feature, clss, pack);
		if (clss == null) {
			page.setRefines(false);
		} else {
			page.setRefines(!clss.isEmpty());
		}
		addPage(page);
	}

	/**
	 * This method is called when 'Finish' button is pressed in the wizard. We will create an operation and run it using wizard as execution context.
	 */
	@Override
	public boolean performFinish() {
		final IContainer container = page.getContainerObject();
		final String fileName = page.getFileName();
		final String fileExtension = page.getExtension();
		final String fileTemplate = page.getTemplate();
		final IComposerExtensionClass composer = page.getComposer();
		final String featureName = page.getFeatureName();
		final String className = page.getClassName();
		final String packageName = page.getPackage();
		IFolder sourceFolder = page.getSourceFolder();
		if (composer.createFolderForFeatures()) {
			sourceFolder = sourceFolder.getFolder(featureName);
		}
		createFolder(page.getPackage(), sourceFolder);
		final IRunnableWithProgress op = new IRunnableWithProgress() {

			@Override
			public void run(IProgressMonitor monitor) throws InvocationTargetException {
				try {
					doFinish(featureName, container, fileName, className, fileExtension, fileTemplate, composer, page.isRefinement(), packageName, monitor);
				} catch (final CoreException e) {
					throw new InvocationTargetException(e);
				} finally {
					monitor.done();
				}
			}
		};
		try {
			getContainer().run(true, false, op);
		} catch (final InterruptedException e) {
			return false;
		} catch (final InvocationTargetException e) {
			final Throwable realException = e.getTargetException();
			MessageDialog.openError(getShell(), "Error", realException.getMessage());
			return false;
		}
		return true;
	}

	/**
	 * @param packageName
	 * @param sourceFolder
	 */
	private void createFolder(String packageName, IFolder folder) {
		for (final String p : packageName.split("[.]")) {
			folder = folder.getFolder(p);
			if (!folder.exists()) {
				try {
					folder.create(true, true, null);
				} catch (final CoreException e) {
					UIPlugin.getDefault().logError(e);
				}
			}
		}
	}

	/**
	 * The worker method. It will find the container, create the file if missing or just replace its contents, and open the editor on the newly created file.
	 *
	 * @param packageName
	 */
	private void doFinish(String featureName, IContainer container, String fileName, String classname, String extension, String template,
			IComposerExtensionClass composer, boolean refines, String packageName, IProgressMonitor monitor) throws CoreException {
		// create a sample file
		monitor.beginTask(CREATING + fileName, 2);
		final IFile file = container.getFile(new Path(fileName + "." + extension));

		try {
			final InputStream stream = openContentStream(featureName, container, classname, template, composer, refines, packageName);
			if (file.exists()) {
				file.setContents(stream, true, true, monitor);
			} else {
				file.create(stream, true, monitor);
			}
			stream.close();
		} catch (final IOException e) {}
		monitor.worked(1);
		monitor.setTaskName(OPENING_FILE_FOR_EDITING___);
		getShell().getDisplay().asyncExec(new Runnable() {

			@Override
			public void run() {
				final IWorkbenchPage page = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
				try {
					IDE.openEditor(page, file, true);
				} catch (final PartInitException e) {}
			}
		});
		monitor.worked(1);
	}

	// TODO Rename, method name does not describe the functionality
	private InputStream openContentStream(String featurename, IContainer container, String classname, String template, IComposerExtensionClass composer,
			boolean refines, String packageName) {
		String contents = template;
		contents = composer.replaceSourceContentMarker(contents, refines, packageName);
		contents = contents.replaceAll(IComposerExtensionClass.CLASS_NAME_PATTERN, classname);
		contents = contents.replaceAll(IComposerExtensionClass.FEATUE_PATTER, featurename);
		return new ByteArrayInputStream(contents.getBytes(Charset.availableCharsets().get("UTF-8")));
	}

	/**
	 * We will accept the selection in the workbench to see if we can initialize from it.
	 *
	 * @see IWorkbenchWizard#init(IWorkbench, IStructuredSelection)
	 */
	@Override
	public void init(IWorkbench workbench, IStructuredSelection selection) {
		this.selection = selection;
	}

	/**
	 * Extended for passing selected feature.
	 *
	 * @see IWorkbenchWizard#init(IWorkbench, IStructuredSelection)
	 */
	public void init(IWorkbench workbench, IStructuredSelection selection, String feature, String clss, String pack) {
		this.selection = selection;
		this.feature = feature;
		this.clss = clss;
		this.pack = pack;
	}
}
