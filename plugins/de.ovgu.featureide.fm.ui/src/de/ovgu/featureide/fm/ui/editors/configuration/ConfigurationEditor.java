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
package de.ovgu.featureide.fm.ui.editors.configuration;

import static de.ovgu.featureide.fm.core.localization.StringTable.SELECT_THE_CORRESPONDING_FEATUREMODEL_;

import java.io.File;
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
import de.ovgu.featureide.fm.core.configuration.ConfigurationPropagator;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.functional.Functional.ICriticalConsumer;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager.FeatureModelSnapshot;
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

	private final JobSynchronizer configJobManager = new JobSynchronizer();

	private final List<IConfigurationEditorPage> allPages = new ArrayList<>(5);
	private List<IConfigurationEditorPage> extensionPages;
	private List<IConfigurationEditorPage> internalPages;
	private TextEditorPage textEditorPage;

	/**
	 * The file of the corresponding feature model.
	 */
	private File modelFile;
	private IFile file;
	private ModelMarkerHandler<IFile> markerHandler;

	private ConfigurationManager configurationManager;
	private FeatureModelManager featureModelManager;
	private FeatureModelSnapshot featureModelSnapshot;

	private EXPAND_ALGORITHM currentExpandAlgorithm = EXPAND_ALGORITHM.DEFUALT;

	private int currentPageIndex = -1;

	private boolean autoSelectFeatures = true;
	private boolean invalidFeatureModel = true;
	private boolean containsError = false;

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
			if (configurationManager != null) {
				configurationManager.removeListener(ConfigurationEditor.this);
				configurationManager.override();
			}
			FeatureColorManager.removeListener(ConfigurationEditor.this);
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

	public List<IConfigurationEditorPage> getExtensionPages() {
		return extensionPages;
	}

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
		FeatureColorManager.addListener(this);
		super.setInput(input);
		getSite().getPage().addPartListener(iPartListener);
		final IProject project = file.getProject();
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

				modelFile = new File(path);

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

					modelFile = new File(path);

					setModelFile(path);
				}
			}
		}
		final Path modelPath = Paths.get(res.getLocationURI());

		configurationManager = ConfigurationManager.getInstance(Paths.get(file.getLocationURI()), modelPath);
		featureModelManager = configurationManager.getFeatureModelManager();
		featureModelSnapshot = featureModelManager.getSnapshot();
		invalidFeatureModel = featureModelManager.getLastProblems().containsError();
		if (invalidFeatureModel) {
			return;
		}

		//TODO mapping model
		//		if (mappingModel) {
		//			featureModelManager = FeatureModelManager.getInstance(absolutePath, format);
		//			featureModel = ((ExtendedFeatureModel) featureModel).getMappingModel();
		//		}

		final ProblemList lastProblems = configurationManager.getLastProblems();
		createModelFileMarkers(lastProblems);
		setContainsError(lastProblems.containsError());

		featureModelManager.addListener(this);
		configurationManager.addListener(this);
		firePropertyChange(IEditorPart.PROP_DIRTY);
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
	private String openFileDialog() {
		FileDialog dialog = new FileDialog(getSite().getWorkbenchWindow().getShell(), SWT.MULTI);
		dialog.setText(SELECT_THE_CORRESPONDING_FEATUREMODEL_);
		dialog.setFileName("model.xml");
		final ArrayList<String> suffixes = new ArrayList<>();
		final ArrayList<String> names = new ArrayList<>();
		for (IFeatureModelFormat extension : FMFormatManager.getInstance().getExtensions()) {
			if (extension.supportsRead()) {
				suffixes.add("*." + extension.getSuffix());
				names.add(extension.getName() + " *." + extension.getSuffix());
			}
		}
		dialog.setFilterExtensions(suffixes.toArray(new String[0]));
		dialog.setFilterNames(names.toArray(new String[0]));
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

	@Override
	public void propertyChange(final FeatureIDEEvent evt) {
		switch (evt.getEventType()) {
		case MODEL_DATA_SAVED:
		case MODEL_DATA_OVERRIDDEN:
		case COLOR_CHANGED:
			if (evt.getSource() instanceof IFeatureModel) {
				final Configuration configuration = new Configuration(configurationManager.getObject(), featureModelManager.getObject());
				configurationManager.setObject(configuration);
				setContainsError(false);

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
		default:
			break;
		}
	}

	@Override
	protected void createPages() {
		if (modelFile != null) {
			allPages.add(initPage(new ConfigurationPage()));
			allPages.add(initPage(new AdvancedConfigurationPage()));
		}
		textEditorPage = (TextEditorPage) initPage(new TextEditorPage());
		allPages.add(textEditorPage);
		internalPages = allPages.subList(0, allPages.size());

		IConfigurationElement[] config = Platform.getExtensionRegistry().getConfigurationElementsFor(FMUIPlugin.PLUGIN_ID + ".ConfigurationEditor");
		try {
			for (IConfigurationElement e : config) {
				final Object o = e.createExecutableExtension("class");
				if (o instanceof IConfigurationEditorPage) {
					final IConfigurationEditorPage externalPage = initPage(((IConfigurationEditorPage) o));
					allPages.add(externalPage);
					externalPage.propertyChange(null);
				}
			}
		} catch (Exception e) {
			FMCorePlugin.getDefault().logError(e);
		}
		extensionPages = allPages.subList(internalPages.size(), allPages.size());

		if (containsError()) {
			setActivePage(textEditorPage.getIndex());
		} else if (requiresAdvancedConfigurationPage()) {
			setActivePage(internalPages.get(1).getIndex());
		}
	}

	private boolean requiresAdvancedConfigurationPage() {
		for (SelectableFeature feature : configurationManager.editObject().getFeatures()) {
			if (feature.getManual() == Selection.UNSELECTED) {
				return true;
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
			for (IConfigurationEditorPage internalPage : allPages) {
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
					configurationManager.externalSave(new ICriticalConsumer<Configuration>() {
						@Override
						public void invoke(Configuration t) throws Exception {
							for (IConfigurationEditorPage internalPage : allPages) {
								if (internalPage != currentPage) {
									internalPage
											.propertyChange(new FeatureIDEEvent(t, FeatureIDEEvent.EventType.MODEL_DATA_SAVED));
								}
							}
							currentPage.doSave(monitor);
						}
					});
				}
			} else {
				configurationManager.save();
				for (IConfigurationEditorPage internalPage : allPages) {
					if (internalPage != currentPage) {
						internalPage.propertyChange(new FeatureIDEEvent(configurationManager.editObject(), FeatureIDEEvent.EventType.MODEL_DATA_SAVED));
					}
				}
				currentPage.doSave(monitor);
			}
		} else {
			for (IConfigurationEditorPage internalPage : allPages) {
				internalPage.doSave(monitor);
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
				if (inputFileDelta != null && (inputFileDelta.getFlags() & IResourceDelta.REMOVED) == 0) {
					closeEditor(input);
				}
			} else if ((event.getType() == IResourceChangeEvent.PRE_CLOSE) && inputFile.getProject().equals(event.getResource())) {
				closeEditor(input);
			}
		}
	}

	private void closeEditor(final IEditorInput input) {
		Display.getDefault().asyncExec(new Runnable() {
			public void run() {
				if (getSite() != null && getSite().getWorkbenchWindow() != null) {
					for (IWorkbenchPage page : getSite().getWorkbenchWindow().getPages()) {
						page.closeEditor(page.findEditor(input), true);
					}
				}
			}
		});
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

	public boolean containsError() {
		return containsError;
	}

	public void setContainsError(boolean containsError) {
		this.containsError = containsError;
	}

	@Override
	public ConfigurationPropagator getPropagator() {
		return featureModelSnapshot.getPropagator(getConfiguration());
	}

	public ConfigurationManager getConfigurationManager() {
		return configurationManager;
	}

}
