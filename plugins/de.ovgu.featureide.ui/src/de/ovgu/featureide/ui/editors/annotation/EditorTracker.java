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
package de.ovgu.featureide.ui.editors.annotation;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.HashSet;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IPartListener2;
import org.eclipse.ui.IWindowListener;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartReference;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.part.WorkbenchPart;
import org.eclipse.ui.texteditor.ITextEditor;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * Listens for an editorpart to attach the color annotation model and renaming of titel for java editor
 *
 * @author Sebastian Krieter
 */
public class EditorTracker {

	private static final Image TITLE_IMAGE = UIPlugin.getImage("JakFileIcon.png");
	private final IWorkbench workbench;
	private final HashSet<IWorkbenchPartReference> annotatedPartrefSet = new HashSet<IWorkbenchPartReference>();

	private final IWindowListener windowListener = new IWindowListener() {

		@Override
		public void windowOpened(IWorkbenchWindow window) {
			window.getPartService().addPartListener(partListener);
		}

		@Override
		public void windowClosed(IWorkbenchWindow window) {
			window.getPartService().removePartListener(partListener);
		}

		@Override
		public void windowActivated(IWorkbenchWindow window) {}

		@Override
		public void windowDeactivated(IWorkbenchWindow window) {}
	};

	private final IPartListener2 partListener = new IPartListener2() {

		@Override
		public void partOpened(IWorkbenchPartReference partref) {
			// System.out.println(OPENED+partref.getTitle());

		}

		@Override
		public void partActivated(IWorkbenchPartReference partref) {
			// System.out.println(ACTIVATED +partref.getTitle());
			annotateEditor(partref);
		}

		@Override
		public void partBroughtToTop(IWorkbenchPartReference partref) {
			// System.out.println(TOTOP +partref.getTitle());
		}

		@Override
		public void partVisible(IWorkbenchPartReference partref) {
			// System.out.println(VISIBLE +partref.getTitle());
			try {
				if (annotatedPartrefSet.contains(partref)) {
					updateEditor(partref);
				}
				renameEditor(partref);
			} catch (final Exception e) {
				UIPlugin.getDefault().logError(e);
			}
		}

		@Override
		public void partInputChanged(IWorkbenchPartReference partref) {}

		@Override
		public void partClosed(IWorkbenchPartReference partref) {}

		@Override
		public void partDeactivated(IWorkbenchPartReference partref) {}

		@Override
		public void partHidden(IWorkbenchPartReference partref) {}
	};

	public EditorTracker(IWorkbench workbench) {
		this.workbench = workbench;
		for (final IWorkbenchWindow w : workbench.getWorkbenchWindows()) {
			w.getPartService().addPartListener(partListener);
		}
		workbench.addWindowListener(windowListener);
	}

	public void dispose() {
		workbench.removeWindowListener(windowListener);
		for (final IWorkbenchWindow w : workbench.getWorkbenchWindows()) {
			w.getPartService().removePartListener(partListener);
		}
		annotatedPartrefSet.clear();
	}

	private void annotateEditor(IWorkbenchPartReference partref) {
		final IWorkbenchPart part = partref.getPart(false);
		if (part instanceof ITextEditor) {
			if (ColorAnnotationModel.attach((ITextEditor) part)) {
				annotatedPartrefSet.add(partref);
			}
		}
	}

	private void updateEditor(IWorkbenchPartReference partref) {

		final IWorkbenchPart part = partref.getPart(false);
		if (part != null) {
			final ITextEditor editor = (ITextEditor) part;
			ColorAnnotationModel.attach(editor);
		}
	}

	private void renameEditor(IWorkbenchPartReference partref)
			throws IllegalAccessException, IllegalArgumentException, InvocationTargetException, NoSuchMethodException, SecurityException {
		if (!(partref.getPart(true) instanceof IEditorPart)) {
			return;
		}
		final IEditorPart editorPart = (IEditorPart) partref.getPart(true);
		final IEditorInput input = editorPart.getEditorInput();
		if (!(input instanceof IFileEditorInput)) {
			return;
		}
		final IFile file = ((IFileEditorInput) input).getFile();
		if (file == null) {
			return;
		}
		final String fileExt = file.getFileExtension();
		if ((fileExt == null) || !fileExt.equals("java")) {
			return;
		}
		final IFeatureProject featureProject = CorePlugin.getFeatureProject(file);
		if (featureProject == null) {
			return;
		}
		final String title = getTitle(partref, file);
		final WorkbenchPart workBenchpart = (WorkbenchPart) partref.getPart(false);
		invokeMethod(workBenchpart, "setPartName", String.class, title);
		invokeMethod(workBenchpart, "setTitleImage", Image.class, TITLE_IMAGE);
	}

	/**
	 * Invokes a method using reflection
	 *
	 * @param obj object that is used to call the method
	 * @param methodname name of the method
	 * @param paramtype type of parameter
	 * @param parameter object of parameter
	 * @throws NoSuchMethodException
	 * @throws IllegalAccessException
	 * @throws InvocationTargetException
	 */
	@SuppressWarnings("rawtypes")
	private void invokeMethod(WorkbenchPart obj, String methodname, Class paramtype, Object parameter)
			throws NoSuchMethodException, IllegalAccessException, InvocationTargetException {
		final Method method = WorkbenchPart.class.getDeclaredMethod(methodname, paramtype);
		method.setAccessible(true);
		method.invoke(obj, (paramtype.cast(parameter)));
	}

	private IComposerExtensionClass composer;

	private String getTitle(IWorkbenchPartReference partRef, IFile file) {
		final IFeatureProject featureProject = CorePlugin.getFeatureProject(file);
		if (featureProject != null) {
			if (partRef.getPart(true) instanceof IEditorPart) {

				composer = featureProject.getComposer();
				if (composer.hasFeatureFolder()) {
					final String feature = featureProject.getFeatureName(file);
					if (feature != null) {
						// case: a source file
						if (composer.hasFeatureFolder()) {
							return file.getName() + "[" + feature + "]";
						}
					} else {
						if (isComposedFile(file.getParent(), featureProject.getBuildFolder())) {
							// case: a composed file
							final IFile configuration = featureProject.getCurrentConfiguration();
							if (configuration != null) {
								final String config = configuration.getName().split("[.]")[0];
								if (config != null) {
									return file.getName() + "<" + config + ">";
								}
							}
						} else {
							final String configuration = getConfiguration(file.getParent());
							if (configuration != null) {
								// case: a generated products file
								return file.getName() + "<" + configuration + ">";
							}
						}
					}
				}

			}
		}
		// no change
		return partRef.getTitle();
	}

	/**
	 * Looks for the corresponding configuration file<br> Necessary for generated products
	 *
	 * @param parent
	 * @return The name of the configuration or <code>null</code> if there is none
	 */
	private String getConfiguration(IContainer parent) {
		try {
			for (final IResource res : parent.members()) {
				if (res instanceof IFile) {
					if (composer.getConfigurationExtension().equals(res.getFileExtension())) {
						return res.getName().split("[.]")[0];
					}
				}
			}
		} catch (final CoreException e) {
			UIPlugin.getDefault().logError(e);
		}
		final IContainer p = parent.getParent();
		if (p != null) {
			return getConfiguration(p);
		}
		return null;
	}

	/**
	 * @param parent
	 * @param buildFolder
	 * @return <code>true</code> if the build folder is a parent of the given file
	 */
	private boolean isComposedFile(IContainer parent, IFolder buildFolder) {
		if (parent != null) {
			if (parent.equals(buildFolder)) {
				return true;
			} else {
				return isComposedFile(parent.getParent(), buildFolder);
			}
		}
		return false;
	}
}
