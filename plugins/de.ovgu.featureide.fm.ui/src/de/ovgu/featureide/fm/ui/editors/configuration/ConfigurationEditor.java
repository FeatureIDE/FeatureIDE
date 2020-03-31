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
package de.ovgu.featureide.fm.ui.editors.configuration;

import static de.ovgu.featureide.fm.core.localization.StringTable.SELECT_THE_CORRESPONDING_FEATUREMODEL_;

import java.io.File;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import javax.annotation.CheckForNull;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.MultiPageEditorPart;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.ModelMarkerHandler;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.io.EclipseFileSystem;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.job.JobStartingStrategy;
import de.ovgu.featureide.fm.core.job.JobToken;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.ConfigurationEditorErrorPage;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * Displays a configuration file.
 *
 * @author Constanze Adler
 * @author Christian Becker
 * @author Jens Meinicke
 * @author Hannes Smurawsky
 */
public class ConfigurationEditor extends MultiPageEditorPart implements GUIDefaults, IEventListener, IResourceChangeListener, IConfigurationEditor {

	public static final String ID = FMUIPlugin.PLUGIN_ID + ".editors.configuration.ConfigurationEditor";

	private static final QualifiedName MODEL_PATH =
		new QualifiedName(ConfigurationEditor.class.getName() + "#MODEL_PATH", ConfigurationEditor.class.getName() + "#MODEL_PATH");

	private final JobToken configJobToken = LongRunningWrapper.createToken(JobStartingStrategy.CANCEL_WAIT_ONE);

	private final List<IConfigurationEditorPage> allPages = new ArrayList<>(5);
	private List<IConfigurationEditorPage> extensionPages;
	private List<IConfigurationEditorPage> internalPages;
	private TextEditorPage textEditorPage;

	private ModelMarkerHandler<IFile> markerHandler;

	private ConfigurationManager configurationManager;
	private FeatureModelManager featureModelManager;

	private ExpandAlgorithm currentExpandAlgorithm = ExpandAlgorithm.ALL_SELECTED;

	private int currentPageIndex = -1;

	private boolean autoSelectFeatures = true;
	private boolean invalidFeatureModel = true;
	private boolean readConfigurationError = false;
	private boolean readFeatureModelError = false;

	private final IPartListener iPartListener = new IPartListener() {

		@Override
		public void partBroughtToTop(IWorkbenchPart part) {}

		@Override
		public void partClosed(IWorkbenchPart part) {
			LongRunningWrapper.cancelAllJobs(configJobToken);
			if (featureModelManager != null) {
				featureModelManager.removeListener(ConfigurationEditor.this);
			}
			if (configurationManager != null) {
				configurationManager.removeListener(ConfigurationEditor.this);
				configurationManager.overwrite();
			}
			FeatureColorManager.removeListener(ConfigurationEditor.this);
		}

		@Override
		public void partDeactivated(IWorkbenchPart part) {

		}

		@Override
		public void partOpened(IWorkbenchPart part) {}

		@Override
		public void partActivated(IWorkbenchPart part) {}
	};

	public List<IConfigurationEditorPage> getExtensionPages() {
		return extensionPages;
	}

	@Override
	public ExpandAlgorithm getExpandAlgorithm() {
		return currentExpandAlgorithm;
	}

	@Override
	public void setExpandAlgorithm(ExpandAlgorithm expandAlgorithm) {
		currentExpandAlgorithm = expandAlgorithm;
	}

	@Override
	protected void setInput(IEditorInput input) {
		// Cast is necessary for backward compatibility, don't remove
		final IFile file = (IFile) input.getAdapter(IFile.class);
		markerHandler = new ModelMarkerHandler<>(file);

		ResourcesPlugin.getWorkspace().addResourceChangeListener(this);
		FeatureColorManager.addListener(this);
		super.setInput(input);
		setPartName(file.getName());
		getSite().getPage().addPartListener(iPartListener);

		final File modelFile = setFeatureModelFile(file.getProject());

		if (!isReadFeatureModelError()) {
			final Path modelPath = modelFile.toPath();
			featureModelManager = FeatureModelManager.getInstance(modelPath);
			if (featureModelManager != null) {
				invalidFeatureModel = featureModelManager.getLastProblems().containsError();
				if (invalidFeatureModel) {
					return;
				}
			} else {
				setReadFeatureModelError(true);
			}
		}

		configurationManager = ConfigurationManager.getInstance(EclipseFileSystem.getPath(file));
		if (configurationManager != null) {
			if (!isReadFeatureModelError()) {
				configurationManager.linkFeatureModel(featureModelManager);
			}

			final ProblemList lastProblems = configurationManager.getLastProblems();
			createModelFileMarkers(lastProblems);
			setReadConfigurationError(lastProblems.containsError());

			if (!isReadFeatureModelError()) {
				configurationManager.update();
				featureModelManager.addListener(this);
			}
			configurationManager.addListener(this);
			firePropertyChange(IEditorPart.PROP_DIRTY);
		} else {
			setReadConfigurationError(true);
			return;
		}

		if (!isIOError()) {
			final IConfigurationEditorPage page = getPage(getActivePage());
			if (page != null) {
				page.propertyChange(null);
			}
		}
	}

	private File setFeatureModelFile(IProject project) {
		// if mpl.velvet exists then it is a multi product line
		IResource res = project.findMember("mpl.velvet");
		if (res instanceof IFile) {
			// final IContainer parentFolder = file.getParent();
			// mappingModel = parentFolder != null && "InterfaceMapping".equals(parentFolder.getName());
		} else {
			res = project.findMember("model.xml");
		}

		File modelFile = null;
		if (res instanceof IFile) {
			modelFile = ((IFile) res).getLocation().toFile();
		}
		if (modelFile == null) {
			// case: there is no model file found at the project

			// get the path saved at the projects persistent properties
			String path = getPersitentModelFilePath(project);
			if (path == null) {
				// case: there was no path saved for this project
				path = openFileDialog(project);
				if (path == null) {
					setReadFeatureModelError(true);
				} else {
					modelFile = new File(path);
					setReadFeatureModelError(!setModelFile(project, path));
				}
			} else {
				// case: use the saved path
				if (!setModelFile(project, path)) {
					// case: the file does not exist
					path = openFileDialog(project);
					if (path == null) {
						setReadFeatureModelError(true);
						return null;
					}
					modelFile = new File(path);
					setReadFeatureModelError(!setModelFile(project, path));
				}
			}
		}
		if (modelFile == null) {
			setReadFeatureModelError(true);
		}
		return modelFile;
	}

	/**
	 * Sets and saved the model file with the given path
	 *
	 * @param path The path of the model file
	 * @param project
	 * @return <i>false</i> if the file with the given path does not exist
	 */
	private boolean setModelFile(IProject project, String path) {
		if (Files.exists(Paths.get(path))) {
			setPersitentModelFilePath(project, path);
			return true;
		}
		return false;
	}

	/**
	 * Opens a Dialog to select the file of the {@link IFeatureModel}
	 *
	 * @return a string describing the absolute path of the selected model file
	 * @see FileDialog#open()
	 */
	private String openFileDialog(IProject project) {
		if ((project != null) && (project.getLocation() != null)) {
			final FileDialog dialog = new FileDialog(getSite().getWorkbenchWindow().getShell(), SWT.MULTI);
			dialog.setText(SELECT_THE_CORRESPONDING_FEATUREMODEL_);
			dialog.setFileName("model.xml");
			final ArrayList<String> suffixes = new ArrayList<>();
			final ArrayList<String> names = new ArrayList<>();
			for (final IPersistentFormat<IFeatureModel> extension : FMFormatManager.getInstance().getExtensions()) {
				if (extension.supportsRead()) {
					suffixes.add("*." + extension.getSuffix());
					names.add(extension.getName() + " *." + extension.getSuffix());
				}
			}
			dialog.setFilterExtensions(suffixes.toArray(new String[0]));
			dialog.setFilterNames(names.toArray(new String[0]));
			dialog.setFilterPath(project.getLocation().toOSString());
			return dialog.open();
		} else {
			return null;
		}
	}

	/**
	 * Saves the given path at persistent properties of the project
	 *
	 * @param path The path of the models file
	 * @param project
	 */
	private void setPersitentModelFilePath(IProject project, String path) {
		try {
			project.setPersistentProperty(MODEL_PATH, path);
		} catch (final CoreException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

	/**
	 * Gets the models path at persistent properties of the project
	 *
	 * @param project
	 * @return The saved path or {@code null} if there is none.
	 */
	@CheckForNull
	private String getPersitentModelFilePath(IProject project) {
		try {
			return project.getPersistentProperty(MODEL_PATH);
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return null;
	}

	@Override
	public void propertyChange(final FeatureIDEEvent evt) {
		switch (evt.getEventType()) {
		case MODEL_DATA_SAVED:
		case MODEL_DATA_OVERWRITTEN:
		case FEATURE_COLOR_CHANGED:
			if (evt.getSource() instanceof IFeatureModel) {
				configurationManager.update();
				if (configurationManager.hasChanged()) {
					firePropertyChange(IEditorPart.PROP_DIRTY);
				}
				setReadConfigurationError(false);

				// Reinitialize the pages
				final IConfigurationEditorPage currentPage = getPage(currentPageIndex);
				if (currentPage != null) {
					currentPage.propertyChange(evt);
				}
			} else if (evt.getSource() instanceof Configuration) {
				// Reinitialize the pages
				final IConfigurationEditorPage currentPage = getPage(currentPageIndex);
				if (currentPage != null) {
					currentPage.propertyChange(evt);
				}
			}
			break;
		case CONFIGURABLE_ATTRIBUTE_CHANGED:
			if (!evt.getNewValue().equals(evt.getOldValue())) {
				final IConfigurationEditorPage currentPage = getPage(currentPageIndex);
				if (currentPage != null) {
					currentPage.propertyChange(evt);
				}
			}

		default:
			break;
		}
	}

	@Override
	public void setFocus() {
		if (internalPages.get(0) instanceof ConfigurationPage) {
			((ConfigurationPage) internalPages.get(0)).tree.setFocus();
		}
	}

	@Override
	protected void createPages() {
		if (isReadConfigurationError()) {
			internalPages = new ArrayList<>(1);
			if (isReadFeatureModelError()) {
				internalPages.add((ConfigurationEditorErrorPage) initPage(new ConfigurationEditorErrorPage()));
			} else {
				textEditorPage = (TextEditorPage) initPage(new TextEditorPage());
				internalPages.add(textEditorPage);
			}
		} else {
			internalPages = new ArrayList<>(3);
			internalPages.add(initPage(new ConfigurationPage()));
			internalPages.add(initPage(new AdvancedConfigurationPage()));
			textEditorPage = (TextEditorPage) initPage(new TextEditorPage());
			internalPages.add(textEditorPage);
		}
		allPages.addAll(internalPages);

		final IConfigurationElement[] config = Platform.getExtensionRegistry().getConfigurationElementsFor(FMUIPlugin.PLUGIN_ID + ".ConfigurationEditor");
		extensionPages = new ArrayList<>(config.length);
		try {
			for (final IConfigurationElement e : config) {
				final Object o = e.createExecutableExtension("class");
				if (o instanceof IConfigurationEditorPage) {
					extensionPages.add(initPage((IConfigurationEditorPage) o));
				}
			}
		} catch (final Exception e) {
			FMCorePlugin.getDefault().logError(e);
		}
		allPages.addAll(extensionPages);

		if (isIOError()) {
			setActivePage(0);
		} else if (requiresAdvancedConfigurationPage()) {
			setActivePage(internalPages.get(1).getIndex());
		}

		for (final IConfigurationEditorPage externalPage : extensionPages) {
			externalPage.propertyChange(null);
		}
	}

	private boolean requiresAdvancedConfigurationPage() {
		if (configurationManager != null) {
			for (final SelectableFeature feature : configurationManager.getSnapshot().getFeatures()) {
				if (feature.getManual() == Selection.UNSELECTED) {
					return true;
				}
			}
		}
		return false;
	}

	private IConfigurationEditorPage initPage(IConfigurationEditorPage page) {
		page = page.getPage();
		page.setConfigurationEditor(this);
		try {
			page.setIndex(addPage(page, getEditorInput()));
			setPageText(page.getIndex(), page.getPageText());
		} catch (final PartInitException e) {
			FMUIPlugin.getDefault().logError(e);
		}
		return page;
	}

	@Override
	protected void pageChange(int newPageIndex) {
		if (newPageIndex != currentPageIndex) {
			final IConfigurationEditorPage currentPage = getPage(currentPageIndex);
			final IConfigurationEditorPage newPage = getPage(newPageIndex);
			if (currentPage != null) {
				if (currentPage.allowPageChange(newPageIndex)) {
					currentPage.pageChangeFrom(newPageIndex);
				} else {
					setActivePage(currentPageIndex);
					return;
				}
			}
			if (newPage != null) {
				newPage.pageChangeTo(newPageIndex);
			}
			currentPageIndex = newPageIndex;
			super.pageChange(newPageIndex);
		}
	}

	private IConfigurationEditorPage getPage(int pageIndex) {
		if (pageIndex >= 0) {
			for (final IConfigurationEditorPage internalPage : allPages) {
				if (internalPage.getIndex() == pageIndex) {
					return internalPage;
				}
			}
		}
		return null;
	}

	@Override
	public void doSave(final IProgressMonitor monitor) {
		final IConfigurationEditorPage currentPage = getPage(currentPageIndex);
		if (currentPage != null) {
			if (currentPage.getID() == TextEditorPage.ID) {
				if (configurationManager == null) {
					currentPage.doSave(monitor);
				} else {
					textEditorPage.updateConfiguration();
					configurationManager.externalSave(() -> notifyPages(monitor, currentPage));
				}
			} else {
				configurationManager.save();
				notifyPages(monitor, currentPage);
			}
		} else {
			for (final IConfigurationEditorPage internalPage : allPages) {
				internalPage.doSave(monitor);
			}
		}
	}

	private void notifyPages(final IProgressMonitor monitor, final IConfigurationEditorPage currentPage) {
		currentPage.doSave(monitor);
		final Configuration configuration = configurationManager.getSnapshot();
		for (final IConfigurationEditorPage internalPage : allPages) {
			if (internalPage != currentPage) {
				internalPage.propertyChange(new FeatureIDEEvent(configuration, FeatureIDEEvent.EventType.MODEL_DATA_SAVED));
			}
		}
	}

	@Override
	public void doSaveAs() {}

	@Override
	public boolean isSaveAsAllowed() {
		return false;
	}

	@Override
	public void resourceChanged(final IResourceChangeEvent event) {
		if (event.getResource() == null) {
			return;
		}

		final IEditorInput input = getEditorInput();
		if (input instanceof IFileEditorInput) {
			final IFile inputFile = ((IFileEditorInput) input).getFile();

			// Closes editor if resource is deleted
			if ((event.getType() == IResourceChangeEvent.POST_CHANGE) && (event.getResource().getType() == IResource.PROJECT)) {
				final IResourceDelta inputFileDelta = event.getDelta().findMember(inputFile.getFullPath());
				if ((inputFileDelta != null) && ((inputFileDelta.getFlags() & IResourceDelta.REMOVED) == 0)) {
					closeEditor(input);
				}
			} else if ((event.getType() == IResourceChangeEvent.PRE_CLOSE) && inputFile.getProject().equals(event.getResource())) {
				closeEditor(input);
			}
		}
	}

	private void closeEditor(final IEditorInput input) {
		Display.getDefault().asyncExec(new Runnable() {

			@Override
			public void run() {
				if ((getSite() != null) && (getSite().getWorkbenchWindow() != null)) {
					for (final IWorkbenchPage page : getSite().getWorkbenchWindow().getPages()) {
						page.closeEditor(page.findEditor(input), true);
					}
				}
			}
		});
	}

	@Override
	public boolean isAutoSelectFeatures() {
		return autoSelectFeatures;
	}

	@Override
	public void setAutoSelectFeatures(boolean autoSelectFeatures) {
		this.autoSelectFeatures = autoSelectFeatures;
	}

	@Override
	public boolean hasValidFeatureModel() {
		return !invalidFeatureModel;
	}

	void createModelFileMarkers(List<Problem> warnings) {
		markerHandler.deleteAllModelMarkers();
		for (final Problem warning : warnings) {
			markerHandler.createModelMarker(warning.message, warning.severity.getLevel(), warning.line);
		}
	}

	@Override
	public boolean isIOError() {
		return readConfigurationError || readFeatureModelError;
	}

	@Override
	public boolean isReadConfigurationError() {
		return readConfigurationError;
	}

	@Override
	public boolean isReadFeatureModelError() {
		return readFeatureModelError;
	}

	private void setReadFeatureModelError(boolean readFeatureModelError) {
		this.readFeatureModelError = readFeatureModelError;
	}

	void setReadConfigurationError(boolean readConfigurationError) {
		this.readConfigurationError = readConfigurationError;
	}

	@Override
	public ConfigurationManager getConfigurationManager() {
		return configurationManager;
	}

	@Override
	public FeatureModelManager getFeatureModelManager() {
		return featureModelManager;
	}

}
