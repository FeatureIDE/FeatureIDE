/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import javax.annotation.CheckForNull;
import javax.annotation.Nonnull;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
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

import de.ovgu.featureide.fm.core.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationPropagatorJobWrapper.IConfigJob;
import de.ovgu.featureide.fm.core.configuration.ConfigurationReader;
import de.ovgu.featureide.fm.core.configuration.ConfigurationWriter;
import de.ovgu.featureide.fm.core.configuration.FeatureIDEFormat;
import de.ovgu.featureide.fm.core.io.AbstractFeatureModelReader;
import de.ovgu.featureide.fm.core.io.ModelIOFactory;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.job.IJob;
import de.ovgu.featureide.fm.core.job.WorkMonitor;
import de.ovgu.featureide.fm.core.job.util.JobFinishListener;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * Displays a configuration file.
 * 
 * @author Constanze Adler
 * @author Christian Becker
 * @author Jens Meinicke
 * @author Hannes Smurawsky
 */
public class ConfigurationEditor extends MultiPageEditorPart implements GUIDefaults, PropertyConstants, PropertyChangeListener, IResourceChangeListener,
		IConfigurationEditor {

	public static final String ID = FMUIPlugin.PLUGIN_ID + ".editors.configuration.ConfigurationEditor";

	private static final QualifiedName MODEL_PATH = new QualifiedName(ConfigurationEditor.class.getName() + "#MODEL_PATH", ConfigurationEditor.class.getName()
			+ "#MODEL_PATH");

	public ConfigurationPage configurationPage;

	public AdvancedConfigurationPage advancedConfigurationPage;

	private TextEditorPage sourceEditorPage;

	private final ConfigJobManager configJobManager = new ConfigJobManager();

	@Nonnull
	public IFile file;
	private IFile internalFile;

	public FeatureModel featureModel = new FeatureModel();

	public Configuration configuration;

	private int currentPageIndex = -1;

	private boolean closeEditor;

	private boolean autoSelectFeatures = false;

	/**
	 * The file of the corresponding feature model.
	 */
	File modelFile;

	private LinkedList<IConfigurationEditorPage> extensionPages = new LinkedList<IConfigurationEditorPage>();

	/**
	 * @return the extensionPages
	 */
	public LinkedList<IConfigurationEditorPage> getExtensionPages() {
		return extensionPages;
	}

	private IPartListener iPartListener = new IPartListener() {

		@Override
		public void partBroughtToTop(IWorkbenchPart part) {
		}

		@Override
		public void partClosed(IWorkbenchPart part) {
			configJobManager.cancelAllJobs();
			if (featureModel != null) {
				featureModel.removeListener(ConfigurationEditor.this);
			}
		}

		@Override
		public void partDeactivated(IWorkbenchPart part) {
		}

		@Override
		public void partOpened(IWorkbenchPart part) {
		}

		@Override
		public void partActivated(IWorkbenchPart part) {
		}
	};

	@Override
	protected void setInput(IEditorInput input) {
		file = (IFile) input.getAdapter(IFile.class);

		String fileName = file.getName();
		final String extension = file.getFileExtension();
		if (extension != null) {
			fileName = "." + fileName.substring(0, fileName.length() - (extension.length())) + FeatureIDEFormat.EXTENSION;
		} else {
			fileName = "." + fileName + "." + FeatureIDEFormat.EXTENSION;
		}
		internalFile = file.getParent().getFile(Path.fromOSString(fileName));

		ResourcesPlugin.getWorkspace().addResourceChangeListener(this);
		super.setInput(input);
		getSite().getPage().addPartListener(iPartListener);
		IProject project = file.getProject();

		// if mpl.velvet exists then it is a multi product line
		IResource res = project.findMember("mpl.velvet");
		boolean mappingModel = false;
		if (res != null && res instanceof IFile) {
			featureModel = new ExtendedFeatureModel();
			IContainer parentFolder = file.getParent();
			mappingModel = parentFolder != null && "InterfaceMapping".equals(parentFolder.getName());
		} else {
			res = project.findMember("model.xml");
			featureModel = new FeatureModel();
		}

		if (res instanceof IFile) {
			modelFile = ((IFile) res).getLocation().toFile();
		}

		if (modelFile == null) {
			// case: there is no model file found at the project

			// get the path saved at the projects persistent properties
			String path = getPersitentModelFilePath();
			if (path == null) {
				// case: there was no path saved for this project
				path = openFileDialog();
				if (path == null) {
					return;
				}
				if (!setModelFile(path)) {
					return;
				}
			} else {
				// case: use the saved path
				if (!setModelFile(path)) {
					// case: the file does not exist
					path = openFileDialog();
					if (path == null) {
						return;
					}
					setModelFile(path);
				}
			}
		}

		readFeatureModel();
		if (mappingModel) {
			featureModel = ((ExtendedFeatureModel) featureModel).getMappingModel();
		}

		configuration = new Configuration(featureModel, Configuration.PARAM_IGNOREABSTRACT | Configuration.PARAM_LAZY);
		try {
			ConfigurationReader reader = new ConfigurationReader(configuration);
			if (!internalFile.exists() || !reader.readFromFile(internalFile)) {
				reader.readFromFile(file);
			}
		} catch (Exception e) {
			FMCorePlugin.getDefault().logError(e);
		}

		final Display currentDisplay = Display.getCurrent();
		final IConfigJob<?> configJob = configuration.getPropagator().getJobWrapper().load();
		configJob.addJobFinishedListener(new JobFinishListener() {
			@Override
			public void jobFinished(IJob finishedJob, boolean success) {
				autoSelectFeatures = true;
				currentDisplay.asyncExec(new Runnable() {
					@Override
					public void run() {
						getPage(getActivePage()).propertyChange(null);
					}
				});
			}
		});
		configJobManager.startJob(configJob);

		setPartName(file.getName());
		featureModel.addListener(this);
		firePropertyChange(IEditorPart.PROP_DIRTY);
		getExtensions();
	}

	/**
	 * Sets and saved the model file with the given path
	 * 
	 * @param path
	 *            The path of the model file
	 * @return <i>false</i> if the file with the given path does not exist
	 */
	private boolean setModelFile(String path) {
		File file = new File(path);
		if (file.exists()) {
			modelFile = file;
			setPersitentModelFilePath(path);
			return true;
		}
		return false;
	}

	/**
	 * Opens a Dialog to select the file of the {@link FeatureModel}
	 * 
	 * @return a string describing the absolute path of the selected model file
	 * @see FileDialog#open()
	 */
	// TODO add all model extensions
	private String openFileDialog() {
		FileDialog dialog = new FileDialog(getSite().getWorkbenchWindow().getShell(), SWT.MULTI);
		dialog.setText("Select the corresponding Featuremodel.");
		dialog.setFileName("model.xml");
		dialog.setFilterExtensions(new String[] { "*.xml", "*.velvet" });
		dialog.setFilterNames(new String[] { "XML *.xml", "VELVET *.velvet" });
		dialog.setFilterPath(file.getProject().getLocation().toOSString());
		return dialog.open();
	}

	/**
	 * Saves the given path at persistent properties of the project
	 * 
	 * @param path
	 *            The path of the models file
	 */
	private void setPersitentModelFilePath(String path) {
		try {
			file.getProject().setPersistentProperty(MODEL_PATH, path);
		} catch (CoreException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

	/**
	 * Gets the models path at persistent properties of the project
	 * 
	 * @return The saved path or {@code null} if there is none.
	 */
	@CheckForNull
	private String getPersitentModelFilePath() {
		try {
			return file.getProject().getPersistentProperty(MODEL_PATH);
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return null;
	}

	/**
	 * Gets all extensions for this extension point.
	 */
	private void getExtensions() {
		IConfigurationElement[] config = Platform.getExtensionRegistry().getConfigurationElementsFor(FMUIPlugin.PLUGIN_ID + ".ConfigurationEditor");
		try {
			for (IConfigurationElement e : config) {
				final Object o = e.createExecutableExtension("class");
				if (o instanceof IConfigurationEditorPage) {
					extensionPages.add(((IConfigurationEditorPage) o));
				}
			}
		} catch (Exception e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	@Override
	public void propertyChange(final PropertyChangeEvent evt) {
		if (!PropertyConstants.MODEL_DATA_CHANGED.equals(evt.getPropertyName())) {
			return;
		}

		final Object source = evt.getSource();
		if (!(source instanceof IFile) || !((IFile) source).getLocation().toFile().equals(modelFile)) {
			return;
		}

		setConfiguration();

		// Reinitialize the pages
		final IConfigurationEditorPage currentPage = getPage(currentPageIndex);
		if (currentPage != null) {
			currentPage.propertyChange(evt);
		}
	}

	private void setConfiguration() {
		readFeatureModel();
		configuration = new Configuration(configuration, featureModel);
		configuration.getPropagator().update(false, null, new WorkMonitor());
		if (!isDirty()) {
			doSave(null);
		}
	}

	/**
	 * Reads the featureModel from the modelFile.
	 */
	private void readFeatureModel() {
		featureModel.initFMComposerExtension(file.getProject());

		final AbstractFeatureModelReader reader;
		if (featureModel instanceof ExtendedFeatureModel) {
			reader = ModelIOFactory.getModelReader(featureModel, ModelIOFactory.TYPE_VELVET);
		} else {
			reader = ModelIOFactory.getModelReader(featureModel, ModelIOFactory.TYPE_XML);
		}
		try {
			reader.readFromFile(modelFile);
		} catch (FileNotFoundException e) {
			FMUIPlugin.getDefault().logError(e);
		} catch (UnsupportedModelException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

	@Override
	protected void createPages() {
		configurationPage = (ConfigurationPage) initPage(new ConfigurationPage());
		advancedConfigurationPage = (AdvancedConfigurationPage) initPage(new AdvancedConfigurationPage());
		sourceEditorPage = (TextEditorPage) initPage(new TextEditorPage());

		for (IConfigurationEditorPage page : extensionPages) {
			initPage(page).propertyChange(null);
		}
	}

	private IConfigurationEditorPage initPage(IConfigurationEditorPage page) {
		page.setConfigurationEditor(this);
		page = page.getPage();
		try {
			page.setIndex(addPage(page, getEditorInput()));
			setPageText(page.getIndex(), page.getPageText());
		} catch (PartInitException e) {
			FMUIPlugin.getDefault().logError(e);
		}
		return page;
	}

	@Override
	protected void pageChange(int newPageIndex) {
		final IConfigurationEditorPage currentPage = getPage(currentPageIndex);
		if (currentPage != null) {
			currentPage.pageChangeFrom(newPageIndex);
		}

		final IConfigurationEditorPage newPage = getPage(newPageIndex);
		if (newPage != null) {
			newPage.pageChangeTo(newPageIndex);
		}

		currentPageIndex = newPageIndex;
		super.pageChange(newPageIndex);
	}

	private IConfigurationEditorPage getPage(int pageIndex) {
		if (pageIndex == sourceEditorPage.getIndex()) {
			return sourceEditorPage;
		} else if (pageIndex == configurationPage.getIndex()) {
			return configurationPage;
		} else if (pageIndex == advancedConfigurationPage.getIndex()) {
			return advancedConfigurationPage;
		} else if (pageIndex >= 0) {
			for (IConfigurationEditorPage page : extensionPages) {
				if (page.getIndex() == pageIndex) {
					return page;
				}
			}
		}
		return null;
	}

	@Override
	public void doSave(IProgressMonitor monitor) {
		try {
			ConfigurationWriter writer = new ConfigurationWriter(configuration);
			writer.saveToFile(file);
			writer.saveToFile(internalFile);
			firePropertyChange(IEditorPart.PROP_DIRTY);
		} catch (CoreException e) {
			FMUIPlugin.getDefault().logError(e);
		}
		advancedConfigurationPage.doSave(monitor);
		configurationPage.doSave(monitor);
		for (IConfigurationEditorPage page : extensionPages) {
			page.doSave(monitor);
		}
		sourceEditorPage.doSave(monitor);
	}

	@Override
	public void doSaveAs() {
	}

	@Override
	public boolean isSaveAsAllowed() {
		return false;
	}

	public void resourceChanged(IResourceChangeEvent event) {
		if (event.getResource() == null)
			return;

		if (event.getResource().getType() == IResource.PROJECT)
			closeEditor = true;
		final IEditorInput input = getEditorInput();
		if (!(input instanceof IFileEditorInput))
			return;
		final IFile jmolfile = ((IFileEditorInput) input).getFile();

		/*
		 * Closes editor if resource is deleted
		 */
		if ((event.getType() == IResourceChangeEvent.POST_CHANGE) && closeEditor) {
			IResourceDelta rootDelta = event.getDelta();
			// get the delta, if any, for the documentation directory
			final List<IResource> deletedlist = new ArrayList<IResource>();
			IResourceDelta docDelta = rootDelta.findMember(jmolfile.getFullPath());
			if (docDelta != null) {
				IResourceDeltaVisitor visitor = new IResourceDeltaVisitor() {
					public boolean visit(IResourceDelta delta) {
						// only interested in removal changes
						if (((delta.getFlags() & IResourceDelta.REMOVED) == 0) && closeEditor) {
							deletedlist.add(delta.getResource());
						}
						return true;
					}
				};
				try {
					docDelta.accept(visitor);
				} catch (CoreException e) {
					FMUIPlugin.getDefault().logError(e);
				}
			}
			if (deletedlist.size() > 0 && deletedlist.contains(jmolfile)) {
				Display.getDefault().asyncExec(new Runnable() {
					public void run() {
						if (getSite() == null)
							return;
						if (getSite().getWorkbenchWindow() == null)
							return;
						IWorkbenchPage[] pages = getSite().getWorkbenchWindow().getPages();
						for (int i = 0; i < pages.length; i++) {
							IEditorPart editorPart = pages[i].findEditor(input);
							pages[i].closeEditor(editorPart, true);
						}
					}
				});
			}
		}

		/*
		 * Closes all editors with this editor input on project close.
		 */
		final IResource res = event.getResource();
		if ((event.getType() == IResourceChangeEvent.PRE_CLOSE) || closeEditor) {
			Display.getDefault().asyncExec(new Runnable() {
				public void run() {
					if (getSite() == null)
						return;
					if (getSite().getWorkbenchWindow() == null)
						return;
					IWorkbenchPage[] pages = getSite().getWorkbenchWindow().getPages();
					for (int i = 0; i < pages.length; i++) {
						if (jmolfile.getProject().equals(res)) {
							IEditorPart editorPart = pages[i].findEditor(input);
							pages[i].closeEditor(editorPart, true);
						}
					}
				}
			});
		}
	}

	@Override
	public Configuration getConfiguration() {
		return configuration;
	}

	@Override
	public IFile getFile() {
		return file;
	}

	@Override
	public File getModelFile() {
		return modelFile;
	}

	public ConfigJobManager getConfigJobManager() {
		return configJobManager;
	}

	public boolean isAutoSelectFeatures() {
		return autoSelectFeatures;
	}

	public void setAutoSelectFeatures(boolean autoSelectFeatures) {
		this.autoSelectFeatures = autoSelectFeatures;
	}
}
