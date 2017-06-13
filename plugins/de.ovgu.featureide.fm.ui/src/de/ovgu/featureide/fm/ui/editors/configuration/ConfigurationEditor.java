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
package de.ovgu.featureide.fm.ui.editors.configuration;

import static de.ovgu.featureide.fm.core.localization.StringTable.SELECT_THE_CORRESPONDING_FEATUREMODEL_;

import java.io.File;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import javax.annotation.CheckForNull;

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
import de.ovgu.featureide.fm.core.FeatureProject;
import de.ovgu.featureide.fm.core.ModelMarkerHandler;
import de.ovgu.featureide.fm.core.ProjectManager;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationMatrix;
import de.ovgu.featureide.fm.core.configuration.ConfigurationPropagator;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.job.IJob;
import de.ovgu.featureide.fm.core.job.LongRunningJob;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
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
public class ConfigurationEditor extends MultiPageEditorPart implements GUIDefaults, IEventListener, IResourceChangeListener, IConfigurationEditor {

	public static final String ID = FMUIPlugin.PLUGIN_ID + ".editors.configuration.ConfigurationEditor";

	private static final QualifiedName MODEL_PATH = new QualifiedName(ConfigurationEditor.class.getName() + "#MODEL_PATH",
			ConfigurationEditor.class.getName() + "#MODEL_PATH");

	public ConfigurationPage configurationPage;

	public AdvancedConfigurationPage advancedConfigurationPage;

	private final JobSynchronizer configJobManager = new JobSynchronizer();

	public IFile file;

	ModelMarkerHandler<IFile> markerHandler;

	public FeatureProject featureProject;
	public ConfigurationManager configurationManager;
	public FeatureModelManager featureModelManager;

	private int currentPageIndex = -1;

	private boolean closeEditor;

	private boolean autoSelectFeatures = false;

	public boolean invalidFeatureModel = true;

	private boolean containsError = true;

	/**
	 * The file of the corresponding feature model.
	 */
	File modelFile;

	private final LinkedList<IConfigurationEditorPage> extensionPages = new LinkedList<>();

	private final LinkedList<IConfigurationEditorPage> internalPages = new LinkedList<>();

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
			if (featureModelManager != null) {
				featureModelManager.removeListener(ConfigurationEditor.this);
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

	private EXPAND_ALGORITHM currentExpandAlgorithm = EXPAND_ALGORITHM.DEFUALT;

	@Override
	public EXPAND_ALGORITHM getExpandAlgorithm() {
		return currentExpandAlgorithm;
	}

	public void setExpandAlgorithm(EXPAND_ALGORITHM expandAlgorithm) {
		this.currentExpandAlgorithm = expandAlgorithm;
	}

	@Override
	protected void setInput(IEditorInput input) {
		file = (IFile) input.getAdapter(IFile.class);
		markerHandler = new ModelMarkerHandler<>(file);

		ResourcesPlugin.getWorkspace().addResourceChangeListener(this);
		super.setInput(input);
		getSite().getPage().addPartListener(iPartListener);
		IProject project = file.getProject();
		setPartName(file.getName());

		// if mpl.velvet exists then it is a multi product line
		IResource res = project.findMember("mpl.velvet");
		if (res instanceof IFile) {
			//			final IContainer parentFolder = file.getParent();
			//			mappingModel = parentFolder != null && "InterfaceMapping".equals(parentFolder.getName());
		} else {
			res = project.findMember("model.xml");
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
		final Path path = Paths.get(res.getLocationURI());
		
		if (ProjectManager.hasProjectData(path)) {
			featureProject = ProjectManager.getProject(path);
		} else {
			featureProject = ProjectManager.addProject(Paths.get(project.getLocationURI()), path);
		}
		
		configurationManager = (ConfigurationManager) featureProject.getConfigurationManager(file.getLocation().toOSString());

		featureModelManager = FeatureModelManager.getInstance(path);
		invalidFeatureModel = featureModelManager.getLastProblems().containsError();
		if (invalidFeatureModel) {
			return;
		}

		//TODO mapping model
		//		if (mappingModel) {
		//			featureModelManager = FeatureModelManager.getInstance(absolutePath, format);
		//			featureModel = ((ExtendedFeatureModel) featureModel).getMappingModel();
		//		}

		final Configuration c;

//		final IFeatureGraph fg = loadFeatureGraph(res.getLocation().removeLastSegments(1).append("model.fg"));
//		if (fg == null) {
//			c = new Configuration(featureModelManager.getObject(), Configuration.PARAM_IGNOREABSTRACT | Configuration.PARAM_LAZY);
//			configurationManager = FileManagerMap.<Configuration, ConfigurationManager> getInstance(file.getLocation().toOSString());
//			if (configurationManager != null) {
//				configurationManager.setConfiguration(c);
//				configurationManager.read();
//			} else {
//				configurationManager = ConfigurationManager.getInstance(c, file.getLocation().toOSString());
//			}
//		} else {
//			c = new ConfigurationFG(featureModelManager.getObject(), fg, ConfigurationFG.PARAM_IGNOREABSTRACT | ConfigurationFG.PARAM_LAZY);
//		}

		final ProblemList lastProblems = configurationManager.getLastProblems();
		createModelFileMarkers(lastProblems);
		setContainsError(lastProblems.containsError());

		featureModelManager.addListener(this);
		firePropertyChange(IEditorPart.PROP_DIRTY);
		getExtensions();

		loadPropagator();
	}

	public void loadPropagator() {
		featureProject.getStatus().getPropagator(configurationManager.editObject());
//		if (!configurationManager.editObject().getPropagator().isLoaded()) {
//			final Display currentDisplay = Display.getCurrent();
//			LongRunningJob<Void> configJob = new LongRunningJob<>("Load Propagator", configurationManager.editObject().getPropagator().load());
//			configJob.addJobFinishedListener(new JobFinishListener<Void>() {
//				@Override
//				public void jobFinished(IJob<Void> finishedJob) {
//					autoSelectFeatures = true;
//					currentDisplay.asyncExec(new Runnable() {
//						@Override
//						public void run() {
//							getPage(getActivePage()).propertyChange(null);
//						}
//					});
//				}
//			});
//			configJobManager.startJob(configJob, true);
//		}
	}

	// XXX Clause: FG
	private IFeatureGraph loadFeatureGraph(Path path) {
		return null;
//		final IFeatureGraph featureGraph = new MatrixFeatureGraph();
//		final FeatureGraphFormat format = new FeatureGraphFormat();
//		if (FileHandler.load(path, featureGraph, format).containsError()) {
//			return null;
//		} else {
//			return featureGraph;
//		}
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
	 * Opens a Dialog to select the file of the {@link IFeatureModel}
	 * 
	 * @return a string describing the absolute path of the selected model file
	 * @see FileDialog#open()
	 */
	// TODO add all model extensions
	private String openFileDialog() {
		FileDialog dialog = new FileDialog(getSite().getWorkbenchWindow().getShell(), SWT.MULTI);
		dialog.setText(SELECT_THE_CORRESPONDING_FEATUREMODEL_);
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
	public void propertyChange(final FeatureIDEEvent evt) {
		if (!EventType.MODEL_DATA_SAVED.equals(evt.getEventType())) {
			return;
		}

		// TODO?
//		configurationManager.read();
//		final Configuration configuration = new Configuration(configurationManager.getObject(), featureModelManager.getObject());
//		configuration.loadPropagator();
//		LongRunningWrapper.runMethod(configuration.getPropagator().resolve());
//
//		configurationManager.setObject(configuration);
//		setContainsError(configurationManager.getLastProblems().containsError());

		// Reinitialize the pages
		final IConfigurationEditorPage currentPage = getPage(currentPageIndex);
		if (currentPage != null) {
			currentPage.propertyChange(evt);
		}
	}

	@Override
	protected void createPages() {
		if (modelFile != null) {
			internalPages.add(initPage(new ConfigurationPage()));
			internalPages.add(initPage(new AdvancedConfigurationPage()));
		}
		internalPages.add(initPage(new TextEditorPage()));

		for (IConfigurationEditorPage page : extensionPages) {
			initPage(page).propertyChange(null);
		}

		if (containsError()) {
			setActivePage(2);
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
			for (IConfigurationEditorPage internalPage : internalPages) {
				if (internalPage.getIndex() == pageIndex) {
					return internalPage;
				}
			}
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
		if (modelFile != null) {
			final IConfigurationEditorPage currentPage = getPage(currentPageIndex);
			if (currentPage != null && currentPage.getID() == TextEditorPage.ID) {
				currentPage.doSave(monitor);
			} else {
				configurationManager.save();
				for (IConfigurationEditorPage internalPage : internalPages) {
					internalPage.doSave(monitor);
				}
				for (IConfigurationEditorPage page : extensionPages) {
					page.doSave(monitor);
				}
			}
		}
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
		return configurationManager.editObject();
	}

	@Override
	public IFile getFile() {
		return file;
	}

	@Override
	public File getModelFile() {
		return modelFile;
	}

	public JobSynchronizer getConfigJobManager() {
		return configJobManager;
	}

	public boolean isAutoSelectFeatures() {
		return autoSelectFeatures;
	}

	public void setAutoSelectFeatures(boolean autoSelectFeatures) {
		this.autoSelectFeatures = autoSelectFeatures;
	}

	@Override
	public boolean hasValidFeatureModel() {
		return !invalidFeatureModel;
	}

	void createModelFileMarkers(List<Problem> warnings) {
		markerHandler.deleteAllModelMarkers();
		for (Problem warning : warnings) {
			markerHandler.createModelMarker(warning.message, warning.severity.getLevel(), warning.line);
		}
	}

	public ConfigurationMatrix getConfigurationMatrix() {
		ConfigurationMatrix matrix = new ConfigurationMatrix(featureModelManager.getObject(), Paths.get(file.getParent().getLocationURI()));
		matrix.readConfigurations(file.getName());
		return matrix;
	}
	
	public ProblemList checkSource(CharSequence source) {
		final Configuration configuration = getConfiguration();
		final IPersistentFormat<Configuration> confFormat = configurationManager.getFormat();

		final ProblemList problems = confFormat.getInstance().read(configuration, source);
		createModelFileMarkers(problems);
		setContainsError(problems.containsError());

		return problems;
	}

	public boolean containsError() {
		return containsError;
	}

	private void setContainsError(boolean containsError) {
		this.containsError = containsError;
	}

	@Override
	public ConfigurationPropagator getPropagator() {
		return featureProject.getStatus().getPropagator(getConfiguration());
	}

}
