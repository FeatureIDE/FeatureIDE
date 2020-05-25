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
package de.ovgu.featureide.core.internal;

import static de.ovgu.featureide.fm.core.localization.StringTable.CALCULATE_CORE_AND_DEAD_FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.CHECKING_CONFIGURATIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.CHECKING_CONFIGURATIONS_FOR_UNUSED_FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.CHECK_VALIDITY_OF;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONFIGURATION_;
import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE_CONFIGURATION_MARKERS;
import static de.ovgu.featureide.fm.core.localization.StringTable.ERROR_WHILE_LOADING_FEATURE_MODEL_FROM;
import static de.ovgu.featureide.fm.core.localization.StringTable.GET_FALSE_OPTIONAL_FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.GET_SELECTION_MATRIX;
import static de.ovgu.featureide.fm.core.localization.StringTable.GET_UNUSED_FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.IS_INVALID;
import static de.ovgu.featureide.fm.core.localization.StringTable.LOAD_MODEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.NO_COMPOSER_COULD_BE_CREATED_FOR_ID;
import static de.ovgu.featureide.fm.core.localization.StringTable.PERFORMING_FULL_BUILD;
import static de.ovgu.featureide.fm.core.localization.StringTable.REFESH_CONFIGURATION_FOLER;
import static de.ovgu.featureide.fm.core.localization.StringTable.REFRESH_COLLABORATION_VIEW;
import static de.ovgu.featureide.fm.core.localization.StringTable.SYNCHRONIZE_FEATURE_MODEL_AND_FEATURE_MODULES;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_FEATURE_MODEL_IS_VOID_COMMA__I_E__COMMA__IT_CONTAINS_NO_PRODUCTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_FEATURE_MODULE_IS_EMPTY__YOU_EITHER_SHOULD_IMPLEMENT_IT_COMMA__MARK_THE_FEATURE_AS_ABSTRACT_COMMA__OR_REMOVE_THE_FEATURE_FROM_THE_FEATURE_MODEL_;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.annotation.CheckForNull;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.resources.ProjectScope;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.IJobManager;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.osgi.service.prefs.BackingStoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.core.builder.ComposerExtensionManager;
import de.ovgu.featureide.core.builder.ExtensibleFeatureProjectBuilder;
import de.ovgu.featureide.core.builder.FeatureProjectNature;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.job.ModelScheduleRule;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.fm.core.FMComposerManager;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.ModelMarkerHandler;
import de.ovgu.featureide.fm.core.Renaming;
import de.ovgu.featureide.fm.core.RenamingsManager;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.base.impl.DefaultFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.base.impl.FeatureModel;
import de.ovgu.featureide.fm.core.base.impl.MultiFeature;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationAnalyzer;
import de.ovgu.featureide.fm.core.configuration.FeatureIDEFormat;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.io.EclipseFileSystem;
import de.ovgu.featureide.fm.core.io.FeatureOrderFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationIO;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelIO;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;
import de.ovgu.featureide.fm.core.io.manager.VirtualFeatureModelManager;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelFormat;
import de.ovgu.featureide.fm.core.job.JobStartingStrategy;
import de.ovgu.featureide.fm.core.job.JobToken;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Class that encapsulates any data and method related to FeatureIDE projects.
 *
 * @author Marcus Leich
 * @author Thomas Thuem
 * @author Tom Brosch
 * @author Marcus Pinnecke (Feature Interface)
 */
public class FeatureProject extends BuilderMarkerHandler implements IFeatureProject, IResourceChangeListener {

	private static final CorePlugin LOGGER = CorePlugin.getDefault();

	private static final String FEATURE_MODULE_MARKER = "de.ovgu.featureide.core.featureModuleMarker";

	public class FeatureModelChangeListner implements IEventListener {

		/**
		 * listens to changed feature names
		 */
		@Override
		public void propertyChange(FeatureIDEEvent evt) {
			switch (evt.getEventType()) {
			case MODEL_DATA_SAVED:
				try {
					final Object source = evt.getSource();
					if (source instanceof IFeatureModel) {
						renameFeature((IFeatureModel) source);
						checkFeatureCoverage();
						checkConfigurations(getAllConfigurations());
						createAndDeleteFeatureFolders();
						composerExtension.postModelChanged();
					}
				} catch (final CoreException e) {
					CorePlugin.getDefault().logError(e);
				}
				break;
			default:
				break;
			}
		}
	}

	/**
	 * the model representation of the model file
	 */
	private final IFeatureModelManager featureModelManager;

	private FSTModel fstModel;

	/**
	 * a folder for the generated files (only needed if the project has only the FeatureIDE Nature)
	 */
	private IFolder binFolder;

	/**
	 * a folder for jar files
	 */
	private final IFolder libFolder;

	/**
	 * a folder for temporary generated files
	 */
	private final IFolder buildFolder;

	/**
	 * a folder containing all configuration files
	 */
	private final Path configFolder;

	/**
	 * a folder for source files
	 */
	private final IFolder sourceFolder;

	private final IProject project;

	private final ModelMarkerHandler<IFile> modelFile;

	private IComposerExtensionClass composerExtension = null;

	// TODO: Implement possibility to change this path
	private final String featureStubPath = "featurestub";

	private boolean configurationUpdate = false;

	@Override
	public String getFeaturestubPath() {
		return featureStubPath;
	}

	/**
	 * If <code>true</code> there is something changed that is relevant for composition.<br> Usually the the folders of the selected features and the actual
	 * configuration file.
	 */
	private boolean buildRelevantChanges = false;

	private Path currentConfiguration = null;

	private final JobToken syncModulesToken = LongRunningWrapper.createToken(JobStartingStrategy.WAIT_ONE);
	private final JobToken checkConfigurationToken = LongRunningWrapper.createToken(JobStartingStrategy.CANCEL_WAIT_ONE);

	private final LongRunningMethod<Boolean> syncModulesJob = new LongRunningMethod<Boolean>() {

		@Override
		public Boolean execute(IMonitor<Boolean> workMonitor) throws Exception {
			try {
				final IFolder folder = sourceFolder;
				featureModelManager.read();
				final IFeatureModel model = featureModelManager.getObject();
				// prevent warnings, if the user has just created a project
				// without any source files
				// TODO This could be removed because the user could use the
				// modeling extension instead
				if (allFeatureModulesEmpty(folder)) {
					folder.deleteMarkers(FEATURE_MODULE_MARKER, true, IResource.DEPTH_ONE);
					return true;
				}
				// set marker for each folder
				if (folder.exists()) {
					workMonitor.setRemainingWork(folder.members().length);
					for (final IResource res : folder.members()) {
						if (res.exists() && (res instanceof IFolder)) {
							setFeatureModuleMarker(model, (IFolder) res);
						}
						workMonitor.step();
					}
				}
			} catch (final CoreException e) {
				LOGGER.logError(e);
			}
			return true;
		}
	};

	private final LongRunningMethod<Boolean> configurationChecker = new LongRunningMethod<Boolean>() {

		@Override
		public Boolean execute(IMonitor<Boolean> workMonitor) throws Exception {
			final IFolder folder = (IFolder) EclipseFileSystem.getResource(configFolder);
			if (folder == null) {
				return false;
			}
			deleteConfigurationMarkers(folder, IResource.DEPTH_ZERO);
			workMonitor.setRemainingWork(7);
			next(CALCULATE_CORE_AND_DEAD_FEATURES, workMonitor);
			final List<String> concreteFeatures = getOptionalConcreteFeatures();
			next(GET_SELECTION_MATRIX, workMonitor);
			final boolean[][] selectionMatrix = getSelectionMatrix(concreteFeatures);
			next(GET_FALSE_OPTIONAL_FEATURES, workMonitor);
			final Collection<String> falseOptionalFeatures = getFalseOptionalConfigurationFeatures(selectionMatrix, concreteFeatures);
			next(GET_UNUSED_FEATURES, workMonitor);
			workMonitor.checkCancel();
			final Collection<String> deadFeatures = getUnusedConfigurationFeatures(selectionMatrix, concreteFeatures);
			next("create marker: dead features", workMonitor);
			if (!deadFeatures.isEmpty()) {
				createConfigurationMarker(folder, MARKER_NEVER_SELECTED + deadFeatures.size() + (deadFeatures.size() > 1 ? " features are " : " feature is ")
					+ "not used: " + createShortMessage(deadFeatures), -1, IMarker.SEVERITY_INFO);
				next("create marker: false optional features", workMonitor);
			}
			if (!falseOptionalFeatures.isEmpty()) {
				createConfigurationMarker(folder,
						MARKER_ALWAYS_SELECTED + falseOptionalFeatures.size() + (falseOptionalFeatures.size() > 1 ? " features are " : " feature is ")
							+ "optional but used in all configurations: " + createShortMessage(falseOptionalFeatures),
						-1, IMarker.SEVERITY_INFO);
			}
			next(REFESH_CONFIGURATION_FOLER, workMonitor);
			workMonitor.done();
			return true;
		}

		private void next(String subTaskName, IMonitor<?> workMonitor) {
			workMonitor.step();
			workMonitor.setTaskName(subTaskName);
		}

		private String createShortMessage(Collection<String> features) {
			final StringBuilder message = new StringBuilder();
			int addedFeatures = 0;
			for (final String feature : features) {
				message.append(feature);
				message.append(", ");
				if (addedFeatures++ >= 10) {
					message.append("...");
					break;
				}
			}
			if ((addedFeatures < 10) && (addedFeatures > 0)) {
				message.delete(message.lastIndexOf(", "), message.lastIndexOf(", ") + 2);
			}

			return message.toString();
		}
	};

	/**
	 * Creating a new ProjectData includes creating folders if they don't exist, registering workspace listeners and initialization of the wrapper object.
	 *
	 * @param aProject the FeatureIDE project
	 */
	public FeatureProject(IProject aProject) {
		super(aProject);
		project = aProject;

		try {
			project.refreshLocal(IResource.DEPTH_ONE, null);
		} catch (final CoreException e) {
			LOGGER.logError(e);
		}

		if (project.getFile("mpl.velvet").exists()) {
			modelFile = new ModelMarkerHandler<>(project.getFile("mpl.velvet"));
		} else {
			modelFile = new ModelMarkerHandler<>(project.getFile("model.xml"));
		}

		final FeatureModelManager instance = FeatureModelManager.getInstance(EclipseFileSystem.getPath(modelFile.getModelFile()));
		if (instance != null) {
			featureModelManager = instance;
			instance.read();
		} else {
			final DefaultFeatureModelFactory factory = DefaultFeatureModelFactory.getInstance();
			final FeatureModel errorFeatureModel = factory.create();
			factory.createFeature(errorFeatureModel, "__Error__");
			featureModelManager = new VirtualFeatureModelManager(errorFeatureModel);
			LOGGER.logError(new IOException("File " + modelFile + " couldn't be read."));
		}

		// initialize project structure
		try {
			// workaround needed for project imports
			project.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (final CoreException e) {
			LOGGER.logError(e);
		}

		final String projectBuildPath = getProjectBuildPath();

		try {
			// just create the bin folder if project hat only the FeatureIDE
			// Nature
			if ((project.getDescription().getNatureIds().length == 1) && project.hasNature(FeatureProjectNature.NATURE_ID)) {
				if (projectBuildPath.isEmpty() && getProjectSourcePath().isEmpty()) {
					binFolder = FMCorePlugin.getFolder(project, "bin");
				}
			}
		} catch (final CoreException e) {
			LOGGER.logError(e);
		}
		libFolder = FMCorePlugin.getFolder(project, "lib");
		buildFolder = FMCorePlugin.getFolder(project, projectBuildPath);
		sourceFolder = FMCorePlugin.getFolder(project, getProjectSourcePath());
		configFolder = EclipseFileSystem.getPath(FMCorePlugin.getFolder(project, getProjectConfigurationPath()));

		fstModel = null;
		// loading model data and listen to changes in the model file
		addModelListener();
		final Job job = new Job(LOAD_MODEL) {

			@Override
			protected IStatus run(IProgressMonitor monitor) {
				if (loadModel()) {
					return Status.OK_STATUS;
				}
				return Status.CANCEL_STATUS;
			}
		};
		job.setPriority(Job.INTERACTIVE);
		job.schedule();

		// make the composer ID a builder argument
		setComposerID(getComposerID());
		setPaths(getProjectSourcePath(), getProjectBuildPath(), getProjectConfigurationPath());

		initCurrentConfiguration();

		final IComposerExtensionClass composer = getComposer();
		// adds the compiler to the feature project if it is an older project
		if (composer != null) {
			if (sourceFolder != null) {
				composer.addCompiler(getProject(), sourceFolder.getProjectRelativePath().toOSString(),
						EclipseFileSystem.getPath(project).relativize(configFolder).toString(), buildFolder.getProjectRelativePath().toOSString());
			}
		}

		// XXX MPL: hack for importing mpl projects
		if (getFeatureModel() instanceof MultiFeatureModel) {
			try {
				modelFile.getModelFile().touch(null);
			} catch (final CoreException e) {
				LOGGER.logError(e);
			}
		}

		featureModelManager.addListener(new FeatureModelChangeListner());
	}

	@Override
	public void dispose() {
		removeModelListener();
	}

	/**
	 * Loads the model again from the file. Attend that all local changes in the model get lost.<br>
	 *
	 * Before loading, all error markers will be deleted and afterwards new ones might be created if some errors occur.
	 */
	synchronized private boolean loadModel() {
		guidslToXML();

		try {
			// modelReader.readFromFile(modelFile.getModelFile());
			getComposer();
			if ((composerExtension != null) && composerExtension.createFolderForFeatures()) {
				createAndDeleteFeatureFolders();
				setAllFeatureModuleMarkers();
			}
			readFeatureOrder();
			return true;
			// } catch (FileNotFoundException e) {
			// modelFile.createModelMarker(e.getMessage(), IMarker.SEVERITY_ERROR, 0);
			// } catch (UnsupportedModelException e) {
			// modelFile.createModelMarker(e.getMessage(), IMarker.SEVERITY_ERROR, e.lineNumber);
		} catch (final CoreException e) {
			LOGGER.logError(ERROR_WHILE_LOADING_FEATURE_MODEL_FROM + modelFile.getModelFile(), e);
		}
		return false;
	}

	/**
	 * Reads the feature order from the deprecated order file if it still exists
	 *
	 * @throws CoreException
	 *
	 */
	private void readFeatureOrder() throws CoreException {
		final IFile orderFile = project.getFile(".order");
		final IFeatureModel featureModel = featureModelManager.getObject();
		if (featureModel.getFeatureOrderList().isEmpty() && !featureModel.getProperty().isFeatureOrderInXML() && orderFile.exists()) {
			SimpleFileHandler.load(EclipseFileSystem.getPath(orderFile), featureModel, new FeatureOrderFormat());
			// write feature order to model
			final Path path = EclipseFileSystem.getPath(modelFile.getModelFile());
			FeatureModelManager.save(featureModel, path, FMFormatManager.getInstance().getFormatByContent(path));
		}

		/*
		 * TODO delete .order file in 2013 delete de.ovgu.featureide.fm.ui.editors .FeatureOrderEditor#writeToOrderFile() and corresponding call see TODOs
		 */
		// if (file.exists()){
		// file.delete();
		// project.refreshLocal(IResource.DEPTH_ONE, null);
		// }
	}

	/**
	 * If the project contains only an old model in guidsl format it will be converted into a .xml
	 */
	private void guidslToXML() {
		final IFile guidslFile = project.getFile("model.m");
		final IFile xmlFile = project.getFile("model.xml");
		if (guidslFile.exists() && !xmlFile.exists()) {
			FeatureModelIO.getInstance().convert(EclipseFileSystem.getPath(guidslFile), EclipseFileSystem.getPath(xmlFile), new XmlFeatureModelFormat());
		}
		// TODO GUIDSL Annotations, should be handled in guidsl format #write
		// if (!guidslReader.getAnnLine().isEmpty()) {
		// ModelMarkerHandler<IFile> modelFile = new ModelMarkerHandler<>(project.getFile("model.m"));
		// for (int i = 0; i < guidslReader.getAnnLine().size(); i++)
		// modelFile.createModelMarker(THIS_ANNOTATION_IS_NOT_SUPPORTED_YET___MOVED_TO_THE_COMMENT_SECTION_, IMarker.SEVERITY_WARNING,
		// guidslReader.getAnnLine().get(i));
		// }
	}

	private void createAndDeleteFeatureFolders() throws CoreException {
		if ((sourceFolder != null) && sourceFolder.isAccessible()) {
			sourceFolder.refreshLocal(IResource.DEPTH_ONE, null);
			final IFeatureModel featureModel = featureModelManager.getObject();
			// create folders for all layers
			if (featureModel instanceof MultiFeatureModel) {
				for (final IFeature feature : featureModel.getFeatures()) {
					if (feature.getStructure().isConcrete() && (feature instanceof MultiFeature) && !((MultiFeature) feature).isFromExtern()) {
						createFeatureFolder(feature.getName());
					}
				}
			} else {
				for (final IFeature feature : featureModel.getFeatures()) {
					if (feature.getStructure().isConcrete()) {
						createFeatureFolder(feature.getName());
					}
				}
			}
			// delete all empty folders which do not anymore belong to layers
			for (final IResource res : sourceFolder.members()) {
				if ((res instanceof IFolder) && res.isAccessible()) {
					final IFeature feature = featureModel.getFeature(res.getName());
					if ((feature == null) || !feature.getStructure().isConcrete()) {
						final IFolder folder = (IFolder) res;
						folder.refreshLocal(IResource.DEPTH_ONE, null);
						if (folder.members().length == 0) {
							folder.delete(false, null);
						}
					}
				}
			}
		}
	}

	private void addModelListener() {
		ResourcesPlugin.getWorkspace().addResourceChangeListener(this, IResourceChangeEvent.POST_CHANGE);
	}

	private void removeModelListener() {
		ResourcesPlugin.getWorkspace().removeResourceChangeListener(this);
	}

	private void createFeatureFolder(String name) {
		try {
			final IFolder folder = sourceFolder.getFolder(name);
			if (!folder.exists() && composerExtension.hasFeatureFolder() && composerExtension.createFolderForFeatures()) {
				folder.create(false, true, null);
				LOGGER.fireFeatureFolderChanged(folder);
			}
		} catch (final CoreException e) {
			modelFile.createModelMarker(e.getMessage(), IMarker.SEVERITY_WARNING, 0);
		}
	}

	private void renameFeature(final IFeatureModel model) {
		final RenamingsManager renamingsManager = model.getRenamingsManager();
		final List<Renaming> renamings = renamingsManager.getRenamings();
		renamingsManager.clear();
		if (renamings.isEmpty()) {
			return;
		}
		final IComposerExtensionClass composer = getComposer();
		boolean renamePerformed = true;
		final IJobManager manager = Job.getJobManager();
		try {
			manager.beginRule(ModelScheduleRule.RULE, null);
			for (final Renaming renaming : renamings) {
				if (!FMComposerManager.getFMComposerExtension(getProject()).performRenaming(renaming.oldName, renaming.newName, project)) {
					renamePerformed = false;
				}
			}
		} finally {
			manager.endRule(ModelScheduleRule.RULE);
		}
		if (!renamePerformed && composer.hasFeatureFolder()) {
			try {
				sourceFolder.refreshLocal(IResource.DEPTH_ONE, null);
				for (final Renaming renaming : renamings) {
					final IFolder folder = sourceFolder.getFolder(renaming.oldName);
					if (folder.isAccessible()) {
						final IPath newPath = sourceFolder.getFolder(renaming.newName).getFullPath();
						folder.move(newPath, true, null);
						folder.refreshLocal(IResource.DEPTH_ZERO, null);
						LOGGER.fireFeatureFolderChanged(folder);
					}
				}
			} catch (final CoreException e) {
				LOGGER.logError(e);
				modelFile.createModelMarker(e.getMessage(), IMarker.SEVERITY_WARNING, 0);
			}
		}
		if (configFolder != null) {
			try {
				configurationUpdate = true;
				Files.walk(configFolder).forEach(path -> adaptConfigurations(path, featureModelManager.getPersistentFormula(), renamings));
				EclipseFileSystem.getResource(configFolder).refreshLocal(IResource.DEPTH_ONE, null);
			} catch (final CoreException | IOException e) {
				LOGGER.logError(e);
			} finally {
				configurationUpdate = false;
			}
		}
	}

	private void adaptConfigurations(Path path, FeatureModelFormula featureModelFormula, List<Renaming> renamings) {
		if (Files.isRegularFile(path) && Files.isWritable(path)) {
			final FileHandler<Configuration> fileHandler = ConfigurationIO.getInstance().getFileHandler(path);
			final IPersistentFormat<Configuration> format = fileHandler.getFormat();
			final Configuration object = fileHandler.getObject();
			object.updateFeatures(featureModelFormula, renamings);
			try {
				Files.write(path, format.getInstance().write(object).getBytes());
			} catch (final IOException e) {
				e.printStackTrace();
			}
			final ConfigurationManager instance = ConfigurationManager.getInstance(path);
			if (instance != null) {
				instance.read();
			}
		}
	}

	@Override
	public String getProjectName() {
		return project.getName();
	}

	public Path initCurrentConfiguration() {
		if ((currentConfiguration == null) || !Files.exists(currentConfiguration)) {
			if (project.exists() && project.isOpen()) {
				if ((configFolder != null) && Files.exists(configFolder)) {
					String configuration = null;
					try {
						configuration = project.getPersistentProperty(configConfigID);
					} catch (final CoreException e) {
						LOGGER.logError(e);
					}
					if (configuration != null) {
						final Path file = configFolder.resolve(configuration);
						if (Files.exists(file)) {
							currentConfiguration = file;
						} else {
							LOGGER.logWarning("Specified current configuration file " + file + " for project " + project.getName() + " does not exist.");
						}
					}
					if (currentConfiguration == null) {
						final List<Path> configs = getAllConfigurations();
						if (!configs.isEmpty()) {
							setCurrentConfiguration(configs.get(0));
						} else {
							LOGGER.logWarning("Failed to get a current configuration. No configuration files found for project " + project.getName() + ".");
							return null;
						}
					}
				} else {
					LOGGER.logWarning("Failed to get a current configuration. No configuration folder found for project " + project.getName() + ".");
					return null;
				}
			} else {
				LOGGER.logWarning("Failed to get the current configuration. Project " + project.getName() + " is not available.");
				return null;
			}
		}
		return currentConfiguration;
	}

	@Override
	public Path getCurrentConfiguration() {
		if ((currentConfiguration == null) || !Files.exists(currentConfiguration)) {
			if (project.exists() && project.isOpen()) {
				if ((configFolder != null) && Files.exists(configFolder)) {
					final String configuration;
					try {
						configuration = project.getPersistentProperty(configConfigID);
					} catch (final CoreException e) {
						LOGGER.logError(e);
						return null;
					}
					if (configuration != null) {
						final Path file = configFolder.resolve(configuration);
						if (Files.exists(file)) {
							currentConfiguration = file;
						} else {
							LOGGER.logWarning("Specified current configuration file " + file + " for project " + project.getName() + " does not exist.");
						}

						final List<Path> configs = getAllConfigurations();
						if (!configs.isEmpty()) {
							setCurrentConfiguration(configs.get(0));
						} else {
							LOGGER.logWarning("Failed to get a current configuration. No configuration files found for project " + project.getName() + ".");
							return null;
						}
					} else {
						LOGGER.logWarning(
								"Failed to get a current configuration. No current configuration file specified for project " + project.getName() + ".");
						return null;
					}
				} else {
					LOGGER.logWarning("Failed to get a current configuration. No configuration folder found for project " + project.getName() + ".");
					return null;
				}
			} else {
				LOGGER.logWarning("Failed to get the current configuration. Project " + project.getName() + " is not available.");
				return null;
			}
		}
		return currentConfiguration;
	}

	@Override
	public Configuration loadCurrentConfiguration() {
		final Path configurationPath = getCurrentConfiguration();
		if (configurationPath != null) {
			final FileHandler<Configuration> fileHandler = ConfigurationIO.getInstance().getFileHandler(configurationPath);
			if (!fileHandler.getLastProblems().containsError()) {
				final Configuration configuration = fileHandler.getObject();
				if (configuration != null) {
					configuration.updateFeatures(featureModelManager.getPersistentFormula());
					return configuration;
				} else {
					LOGGER.logWarning("Failed to parse current configuration " + configurationPath + ".");
				}
			} else {
				LOGGER.logWarning("Failed to read current configuration " + configurationPath + ".");
			}
		}
		return null;
	}

	@Override
	public Configuration loadConfiguration(Path configurationPath) {
		if (configurationPath != null) {
			final FileHandler<Configuration> fileHandler = ConfigurationIO.getInstance().getFileHandler(configurationPath);
			if (!fileHandler.getLastProblems().containsError()) {
				final Configuration configuration = fileHandler.getObject();
				if (configuration != null) {
					configuration.updateFeatures(featureModelManager.getPersistentFormula());
					return configuration;
				} else {
					LOGGER.logWarning("Failed to parse current configuration " + configurationPath + ".");
				}
			} else {
				LOGGER.logWarning("Failed to read current configuration " + configurationPath + ".");
			}
		}
		return null;
	}

	@Override
	public void setCurrentConfiguration(Path file) {
		final boolean performBuild = currentConfiguration != null;
		currentConfiguration = file;

		final String configPath = configFolder.relativize(file).toString();
		try {
			project.setPersistentProperty(configConfigID, configPath);
			LOGGER.fireCurrentConfigurationChanged(this);
		} catch (final CoreException e) {
			LOGGER.logError(e);
		}

		// We need to call the builder here, because for the new configuration,
		// there are possibly no resource build yet or they are not up-to-date.
		// Eclipse calls builders, if a resource as changed, but in this case
		// actually no resource in the file system changes.
		if (performBuild) {
			final LongRunningMethod<Boolean> job = new LongRunningMethod<Boolean>() {

				@Override
				public Boolean execute(IMonitor<Boolean> workMonitor) throws Exception {
					buildRelevantChanges = true;
					try {
						project.build(IncrementalProjectBuilder.FULL_BUILD, null);
					} catch (final CoreException e) {
						LOGGER.logError(e);
					}
					return true;
				}
			};
			LongRunningWrapper.getRunner(job, PERFORMING_FULL_BUILD).schedule();
		}
	}

	@Override
	@CheckForNull
	public String getBuildPath() {
		return buildFolder != null ? buildFolder.getRawLocation().toOSString() : null;
	}

	@Override
	public IFolder getBinFolder() {
		return binFolder;
	}

	@Override
	public IFolder getLibFolder() {
		return libFolder;
	}

	@Override
	public IFolder getBuildFolder() {
		return buildFolder;
	}

	@Override
	public IFolder getConfigFolder() {
		return (IFolder) EclipseFileSystem.getResource(configFolder);
	}

	@Override
	public IFolder getSourceFolder() {
		if (composerExtension.hasSourceFolder()) {
			return sourceFolder;
		} else {
			return buildFolder;
		}
	}

	@Override
	public String getBinPath() {
		return binFolder.getRawLocation().toOSString();
	}

	@Override
	public String getConfigPath() {
		return configFolder.toAbsolutePath().normalize().toString();
	}

	@Override
	public String getSourcePath() {
		return sourceFolder == null ? null : sourceFolder.getRawLocation().toOSString();
	}

	@Override
	public String getFeatureName(IResource resource) {
		return getFolderName(resource, sourceFolder);
	}

	@Override
	public String getConfigName(IResource resource) {
		return getFolderName(resource, buildFolder);
	}

	@Override
	public String getFolderName(IResource resource, IFolder folder) {
		// check whether resource belongs to this project
		if (resource.getProject() != project) {
			return null;
		}
		final IPath path = resource.getFullPath();
		final String segment = path.segment(1);
		if ((segment != null) && segment.equals(folder.getName())) {
			return path.segment(2);
		}
		return null;
	}

	@Override
	public IProject getProject() {
		return project;
	}

	@Override
	public ProjectSignatures getProjectSignatures() {
		if (fstModel != null) {
			return fstModel.getProjectSignatures();
		}
		return null;
	}

	@Override
	public FSTModel getFSTModel() {
		return fstModel;
	}

	@Override
	public IFeatureModel getFeatureModel() {
		return featureModelManager.getObject();
	}

	@Override
	public IFile getModelFile() {
		return modelFile.getModelFile();
	}

	@Override
	public String[] getJavaClassPath() {
		final ArrayList<String> cp = new ArrayList<String>();
		cp.add(".");
		cp.add(binFolder.getRawLocation().toOSString());
		if (libFolder.exists()) { // delete lib folder implementation
			cp.add(libFolder.getRawLocation().toOSString());
			try {
				for (final IResource res : libFolder.members()) {
					if ((res instanceof IFile) && ((IFile) res).getName().endsWith(".jar")) {
						cp.add(res.getRawLocation().toOSString());
					}
				}
			} catch (final CoreException e) {
				LOGGER.logError(e);
			}
		}

		final String[] paths = getAdditionalJavaClassPath();
		for (final String path : paths) {
			cp.add(path);
		}

		return cp.toArray(new String[cp.size()]);
	}

	@Override
	public String[] getAdditionalJavaClassPath() {
		final ArrayList<String> cp = new ArrayList<String>();
		String classPath = null;
		try {
			classPath = project.getPersistentProperty(javaClassPathID);
		} catch (final CoreException e) {
			LOGGER.logError(e);
		}
		if (classPath != null) {
			final String[] paths = classPath.split(";");
			for (final String path : paths) {
				cp.add(path);
			}
		}
		return cp.toArray(new String[cp.size()]);
	}

	/**
	 * refreshes Feature Module Markers for all folders in the source folder
	 *
	 * @param featureModel
	 * @param sourceFolder
	 */
	/*
	 * The first job is waiting for the synchronization job to finish and sets the variable waiting, so the job will finish early. Than a new job is started. If
	 * <syncJob.join()> is called outside of a job the workspace is blocked, because the method has a higher priority than the synchronization job. The goal of
	 * this is that a synchronization can't be executed unnecessarily multiple times.
	 */
	// TODO this should not be called if only markers are changed
	private void setAllFeatureModuleMarkers() {
		if (composerExtension.createFolderForFeatures()) {
			LongRunningWrapper.startJob(syncModulesToken, LongRunningWrapper.getRunner(syncModulesJob, SYNCHRONIZE_FEATURE_MODEL_AND_FEATURE_MODULES));
		}
	}

	/**
	 * creates (or deletes) Feature Module Marker for the specified folder representing a feature module includes markers for: empty folders for concrete
	 * features, non-empty folders for abstract features, folders without corresponding feature.
	 *
	 * @param featureModel
	 * @param folder the folder
	 */
	private void setFeatureModuleMarker(final IFeatureModel featureModel, IFolder folder) {
		final IFeature feature = featureModel.getFeature(folder.getName());
		try {
			folder.deleteMarkers(FEATURE_MODULE_MARKER, true, IResource.DEPTH_ZERO);
		} catch (final CoreException e) {
			LOGGER.logError(e);
		}

		String message = null;
		int severity = IMarker.SEVERITY_WARNING;
		if (feature == null) {
			severity = IMarker.SEVERITY_ERROR;
			message = "The feature module \"" + folder.getName() + "\" has no corresponding feature at the feature model.";
		} else {
			try {
				final int memberCount = folder.members().length;
				if (feature.getStructure().isConcrete() && (memberCount == 0)) {
					message =
						THE_FEATURE_MODULE_IS_EMPTY__YOU_EITHER_SHOULD_IMPLEMENT_IT_COMMA__MARK_THE_FEATURE_AS_ABSTRACT_COMMA__OR_REMOVE_THE_FEATURE_FROM_THE_FEATURE_MODEL_;
				} else if (feature.getStructure().isAbstract() && (memberCount > 0)) {
					message = "This feature module is ignored as \"" + feature.getName() + "\" is marked as abstract.";
				}
			} catch (final CoreException e) {
				LOGGER.logError(e);
			}
		}
		if (message != null) {
			try {
				if ((folder.findMarkers(FEATURE_MODULE_MARKER, false, IResource.DEPTH_ZERO).length == 0) && folder.exists()) {
					final IMarker marker = folder.createMarker(FEATURE_MODULE_MARKER);
					marker.setAttribute(IMarker.MESSAGE, message);
					marker.setAttribute(IMarker.SEVERITY, severity);
				}
			} catch (final CoreException e) {
				LOGGER.logError(e);
			}
		}
	}

	protected boolean allFeatureModulesEmpty(IFolder sourceFolder) throws CoreException {
		if (!sourceFolder.exists()) {
			return false;
		}
		for (final IResource res : sourceFolder.members()) {
			if ((res instanceof IFolder) && (((IFolder) res).members().length > 0)) {
				return false;
			}
		}
		return true;
	}

	@Override
	public void resourceChanged(IResourceChangeEvent event) {
		if ((event.findMarkerDeltas(DELETE_CONFIGURATION_MARKERS, false).length != 0)
			|| (event.findMarkerDeltas(EclipseMarkerHandler.CONFIGURATION_MARKER, false).length != 0)) {
			return;
		}
		// if something in source folder changed
		if ((sourceFolder != null) && (event.getDelta().findMember(sourceFolder.getFullPath()) != null)) {
			// set markers, only if event is not fired from changes to markers
			if ((event.findMarkerDeltas(FEATURE_MODULE_MARKER, false).length == 0) && (composerExtension != null)
				&& composerExtension.createFolderForFeatures()) {
				setAllFeatureModuleMarkers();
			}
		}

		final IPath modelPath = modelFile.getModelFile().getFullPath();
		if (checkModelChange(event.getDelta().findMember(modelPath))) {
			setAllFeatureModuleMarkers();
			return;
		}

		try {
			final IResource configIFolder = EclipseFileSystem.getResource(configFolder);
			if (configIFolder != null) {
				final List<Path> configs = getAllConfigurations();
				final IPath configIPath = configIFolder.getFullPath();
				final IResourceDelta configurationDelta = event.getDelta().findMember(configIPath);
				if (configurationDelta != null) {
					for (final IResourceDelta delta : configurationDelta.getAffectedChildren(IResourceDelta.REMOVED)) {
						CorePlugin.getDefault().logInfo(delta.toString() + " was removed.");
						// if configuration was removed update warnings
						checkFeatureCoverage();
					}
				}
				final List<Path> changedConfigs = new ArrayList<>();
				for (final Path config : configs) {
					final IPath iPath = EclipseFileSystem.getResource(config).getFullPath();
					final IResourceDelta delta = event.getDelta().findMember(iPath);
					if (delta != null) {
						checkFeatureCoverage();
						break;
					}
				}

				final Path currentConfig = getCurrentConfiguration();
				for (final Path config : configs) {
					final IPath iPath = EclipseFileSystem.getResource(config).getFullPath();
					final IResourceDelta delta = event.getDelta().findMember(iPath);
					if ((delta != null) && ((delta.getFlags() & IResourceDelta.CONTENT) != 0)) {
						changedConfigs.add(config);
						if (config.equals(currentConfig)) {
							buildRelevantChanges = true;
						}
					}
				}
				if (!configurationUpdate && !changedConfigs.isEmpty()) {
					LOGGER.fireConfigurationChanged(this);
					checkConfigurations(changedConfigs);
				}
				if (!buildRelevantChanges && (sourceFolder != null) && sourceFolder.isAccessible()) {
					if ((currentConfig != null) && (composerExtension != null) && composerExtension.hasFeatureFolder()) {
						// ignore changes in unselected feature folders
						final FileHandler<Configuration> fileHandler = ConfigurationIO.getInstance().getFileHandler(currentConfig);
						final Configuration currentConfiguration = fileHandler.getObject();
						currentConfiguration.updateFeatures(featureModelManager.getPersistentFormula());

						final Set<String> selectedFeatures = currentConfiguration.getSelectedFeatureNames();
						for (final IResource res : sourceFolder.members()) {
							if (res instanceof IFolder) {
								if (selectedFeatures.contains(res.getName())) {
									checkSourceFolder((IFolder) res, event);
								}
							}
						}
					} else {
						checkSourceFolder(sourceFolder, event);
					}
				}

				if ((composerExtension != null) && (buildFolder != null) && buildFolder.isAccessible()) {
					checkBuildFolder(buildFolder, event);
				}
			}

		} catch (final CoreException e) {
			LOGGER.logError(e);
		}
	}

	/**
	 * checks if something at source folder has been changed, except of marker changes
	 *
	 */
	private void checkSourceFolder(IFolder folder, IResourceChangeEvent event) throws CoreException {
		if (!buildRelevantChanges) {
			final IResourceDelta delta = event.getDelta().findMember(folder.getFullPath());
			if (delta != null) {
				if (delta.getKind() != IResourceDelta.NO_CHANGE) {
					if (checkSourceFolderChanges(folder, event)) {
						buildRelevantChanges = true;
					}
				}
			}
		}
	}

	private boolean checkSourceFolderChanges(IFolder folder, IResourceChangeEvent event) throws CoreException {
		final IResourceDelta d = event.getDelta().findMember(folder.getFullPath());
		if ((d != null) && ((d.getFlags() & IResourceDelta.MARKERS) != 0)) {
			return false;
		}

		for (final IResource res : folder.members()) {
			if (res instanceof IFolder) {
				final IResourceDelta d2 = event.getDelta().findMember(res.getFullPath());
				if (d2 != null) {
					if (d2.getKind() != IResourceDelta.NO_CHANGE) {
						return checkSourceFolderChanges((IFolder) res, event);
					}
				}
			} else {
				final IResourceDelta delta = event.getDelta().findMember(res.getFullPath());
				if (delta != null) {
					if (((delta.getFlags() & IResourceDelta.CONTENT) != 0) || (delta.getKind() == IResourceDelta.ADDED)) {
						return true;
					} else {
						return false;
					}
				}
			}
		}
		return true;
	}

	private void checkBuildFolder(final IFolder folder, final IResourceChangeEvent event) {
		LongRunningWrapper.getRunner(new LongRunningMethod<Boolean>() {

			@Override
			public Boolean execute(IMonitor<Boolean> workMonitor) throws Exception {
				checkBuildFolder(folder);
				return true;
			}

			private void checkBuildFolder(final IFolder folder) throws CoreException {
				if (folder.isAccessible()) {
					for (final IResource res : folder.members()) {
						if (res instanceof IFolder) {
							checkBuildFolder((IFolder) res);
						} else if (res instanceof IFile) {
							final IResourceDelta delta = event.getDelta().findMember(res.getFullPath());
							if (delta != null) {
								composerExtension.postCompile(delta, (IFile) res);
							}
						}
					}
				}
			}
		}, REFRESH_COLLABORATION_VIEW).schedule();
	}

	@Override
	public List<Path> getAllConfigurations() {
		final List<Path> configs = new ArrayList<>();
		if (!Files.isReadable(configFolder)) {
			return configs;
		}
		try {
			Files.walk(configFolder).forEach(path -> addConfiguration(path, configs));
		} catch (final IOException e) {
			LOGGER.logError(e);
		}
		return configs;
	}

	private void addConfiguration(Path path, List<Path> configs) {
		if (Files.isRegularFile(path) && Files.isWritable(path) && ConfigurationManager.isFileSupported(path)) {
			final ConfigurationManager instance = ConfigurationManager.getInstance(path);
			instance.linkFeatureModel(featureModelManager);
			configs.add(path);
		}
	}

	private boolean checkModelChange(IResourceDelta delta) {
		return (delta != null) && ((delta.getFlags() & IResourceDelta.CONTENT) != 0);
	}

	private void checkConfigurations(final List<Path> files) {
		if ((files == null) || files.isEmpty()) {
			return;
		}

		final LongRunningMethod<Boolean> job = new LongRunningMethod<Boolean>() {

			@Override
			public Boolean execute(IMonitor<Boolean> workMonitor) throws Exception {
				workMonitor.setRemainingWork(2);
				final FeatureModelFormula f = featureModelManager.getPersistentFormula();

				final Configuration config = new Configuration(f);
				IMonitor<?> subTask = workMonitor.subTask(1);
				subTask.setTaskName(DELETE_CONFIGURATION_MARKERS);
				subTask.setRemainingWork(files.size());
				for (final Path file : files) {
					deleteConfigurationMarkers(EclipseFileSystem.getResource(file), IResource.DEPTH_ZERO);
					subTask.step();
				}
				subTask.done();
				subTask = workMonitor.subTask(1);
				subTask.setRemainingWork(files.size());
				// check validity
				for (final Path file : files) {
					subTask.setTaskName(CHECK_VALIDITY_OF + " - " + file.getFileName().toString());
					final ProblemList lastProblems = SimpleFileHandler.load(file, config, ConfigFormatManager.getInstance());
					final ConfigurationAnalyzer analyzer = new ConfigurationAnalyzer(f, config);
					analyzer.update();
					if (!analyzer.isValid()) {
						String name = file.getFileName().toString();
						final int extIndex = name.lastIndexOf('.');
						if (extIndex > 0) {
							name = name.substring(0, extIndex);
						}
						final String message = CONFIGURATION_ + name + IS_INVALID;
						createConfigurationMarker(EclipseFileSystem.getResource(file), message, 0, IMarker.SEVERITY_ERROR);
					}
					// create warnings (e.g., for features that are not available anymore)
					for (final Problem warning : lastProblems) {
						createConfigurationMarker(EclipseFileSystem.getResource(file), warning.getMessage(), warning.getLine(), IMarker.SEVERITY_WARNING);
					}
					subTask.step();
				}
				subTask.done();
				workMonitor.done();
				return true;
			}
		};
		LongRunningWrapper.getRunner(job, CHECKING_CONFIGURATIONS).schedule();
	}

	/**
	 * Checks if any concrete feature is used in at least one configuration.
	 */
	// should also be called if a configuration file was removed
	private void checkFeatureCoverage() {
		LongRunningWrapper.startJob(checkConfigurationToken, LongRunningWrapper.getRunner(configurationChecker, CHECKING_CONFIGURATIONS_FOR_UNUSED_FEATURES));
	}

	@Override
	public Collection<String> getFalseOptionalConfigurationFeatures() {
		return getFalseOptionalConfigurationFeatures(getSelectionMatrix(), (List<String>) getOptionalConcreteFeatures());
	}

	public Collection<String> getFalseOptionalConfigurationFeatures(boolean[][] selections, final List<String> concreteFeatures) {
		return checkValidSelections(selections, false, concreteFeatures);
	}

	@Override
	public Collection<String> getUnusedConfigurationFeatures() {
		return getUnusedConfigurationFeatures(getSelectionMatrix(), (List<String>) getOptionalConcreteFeatures());
	}

	public Collection<String> getUnusedConfigurationFeatures(boolean[][] selections, final List<String> concreteFeatures) {
		return checkValidSelections(selections, true, concreteFeatures);
	}

	private List<String> checkValidSelections(boolean[][] selections, boolean selectionState, final List<String> concreteFeatures) {
		if (selections.length == 0) {
			return Collections.emptyList();
		}
		final List<String> falseOptionalFeatures = new ArrayList<>();
		columnLoop: for (int column = 0; column < concreteFeatures.size(); column++) {
			for (int conf = 0; conf < selections.length; conf++) {
				if (selections[conf][column] == selectionState) {
					continue columnLoop;
				}
			}
			falseOptionalFeatures.add(concreteFeatures.get(column));
		}
		return falseOptionalFeatures;
	}

	private boolean[][] getSelectionMatrix() {
		return getSelectionMatrix(getOptionalConcreteFeatures());
	}

	private boolean[][] getSelectionMatrix(final Collection<String> concreteFeatures) {
		final List<Path> configurations = getAllConfigurations();

		final boolean[][] selections = new boolean[configurations.size()][concreteFeatures.size()];
		final FeatureModelFormula featureModel = featureModelManager.getPersistentFormula();

		int row = 0;
		for (final Path file : configurations) {
			final boolean[] currentRow = selections[row++];
			final Configuration configuration = ConfigurationManager.load(file);
			configuration.updateFeatures(featureModel);

			int column = 0;
			for (final String feature : concreteFeatures) {
				final SelectableFeature selectablefeature = configuration.getSelectableFeature(feature);
				if (selectablefeature != null) {
					currentRow[column] = selectablefeature.getSelection() == Selection.SELECTED;
				}
				column++;
			}
		}
		return selections;
	}

	private List<String> getOptionalConcreteFeatures() {
		final FeatureModelFormula persistentFormula = featureModelManager.getPersistentFormula();
		final IFeatureModel featureModel = persistentFormula.getFeatureModel();
		final List<String> concreteFeatures = FeatureUtils.extractConcreteFeaturesAsStringList(featureModel);
		final FeatureModelAnalyzer analyzer = persistentFormula.getAnalyzer();
		final List<IFeature> coreList = analyzer.getCoreFeatures(null);
		final List<IFeature> deadList = analyzer.getDeadFeatures(null);
		for (final IFeature feature : coreList) {
			concreteFeatures.remove(feature.getName());
		}
		for (final IFeature feature : deadList) {
			concreteFeatures.remove(feature.getName());
		}
		return concreteFeatures;
	}

	@Override
	public IComposerExtensionClass getComposer() {
		if (composerExtension == null) {
			final String compositionToolID = getComposerID();
			if (compositionToolID == null) {
				return null;
			}

			final ComposerExtensionManager composerManagerInstance = ComposerExtensionManager.getInstance();
			composerExtension = composerManagerInstance.getComposerById(this, compositionToolID);
			if (composerExtension != null) {
				((ComposerExtensionClass) composerExtension).initialize(this);
			} else {
				CorePlugin.getDefault().logError(new Exception(NO_COMPOSER_COULD_BE_CREATED_FOR_ID + compositionToolID));
			}
		}
		return composerExtension;
	}

	@Override
	public String getProjectConfigurationPath() {
		try {
			String path = project.getPersistentProperty(configFolderConfigID);
			if ((path != null) && !path.isEmpty()) {
				return path;
			}

			path = FMComposerManager.getPath(project, CONFIGS_ARGUMENT);
			if ((path != null) && !path.isEmpty()) {
				return path;
			}
		} catch (final Exception e) {
			LOGGER.logError(e);
		}
		return DEFAULT_CONFIGS_PATH;
	}

	@Override
	public String getProjectBuildPath() {
		try {
			String path = project.getPersistentProperty(buildFolderConfigID);
			if ((path != null) && !path.isEmpty()) {
				return path;
			}

			path = FMComposerManager.getPath(project, BUILD_ARGUMENT);
			if ((path != null) && !path.isEmpty()) {
				return path;
			}
		} catch (final Exception e) {
			LOGGER.logError(e);
		}
		return DEFAULT_BUILD_PATH;
	}

	@Override
	public String getProjectSourcePath() {
		try {
			String path = project.getPersistentProperty(sourceFolderConfigID);
			if ((path != null) && !path.isEmpty()) {
				return path;
			}

			path = FMComposerManager.getPath(project, SOURCE_ARGUMENT);
			if ((path != null) && !path.isEmpty()) {
				return path;
			}
		} catch (final Exception e) {
			LOGGER.logError(e);
		}
		return DEFAULT_SOURCE_PATH;
	}

	@Override
	public String getComposerID() {
		try {
			String id = project.getPersistentProperty(composerConfigID);
			if (id != null) {
				return id;
			}

			for (final ICommand command : project.getDescription().getBuildSpec()) {
				if (FMComposerManager.isFIDEBuilder(command)) {
					id = command.getArguments().get(ExtensibleFeatureProjectBuilder.COMPOSER_KEY);
					if (id != null) {
						return id;
					}
				}
			}

		} catch (final CoreException e) {
			LOGGER.logError(e);
		}
		return null;
	}

	@Override
	public void setPaths(String feature, String src, String configuration) {
		try {
			final IProjectDescription description = project.getDescription();

			final ICommand[] commands = description.getBuildSpec();
			for (final ICommand command : commands) {
				if (FMComposerManager.isFIDEBuilder(command) || command.getBuilderName().equals("org.eclipse.ui.externaltools.ExternalToolBuilder")) {
					final Map<String, String> args = command.getArguments();
					args.put(SOURCE_ARGUMENT, feature);
					args.put(BUILD_ARGUMENT, src);
					args.put(CONFIGS_ARGUMENT, configuration);
					project.setPersistentProperty(IFeatureProject.buildFolderConfigID, src);
					project.setPersistentProperty(IFeatureProject.configFolderConfigID, configuration);
					project.setPersistentProperty(IFeatureProject.sourceFolderConfigID, feature);
					command.setArguments(args);
				}
			}
			description.setBuildSpec(commands);
			project.setDescription(description, null);
		} catch (final CoreException e) {
			LOGGER.logError(e);
		}
	}

	@Override
	public void setComposerID(String composerID) {
		try {
			project.setPersistentProperty(composerConfigID, composerID);
			final IProjectDescription description = project.getDescription();

			final LinkedList<ICommand> newCommandList = new LinkedList<ICommand>();
			boolean added = false;
			for (final ICommand command : description.getBuildSpec()) {
				if (FMComposerManager.isFIDEBuilder(command)) {
					if (!added) {
						final Map<String, String> args = command.getArguments();
						args.put(ExtensibleFeatureProjectBuilder.COMPOSER_KEY, composerID);
						command.setArguments(args);
						// Composer must be the first command
						newCommandList.addFirst(command);
						added = true;
					}
				} else {
					newCommandList.add(command);
				}
			}
			final ICommand[] newCommandArray = new ICommand[newCommandList.size()];
			int i = 0;
			for (final ICommand c : newCommandList) {
				newCommandArray[i] = c;
				i++;
			}
			description.setBuildSpec(newCommandArray);
			project.setDescription(description, null);
		} catch (final CoreException ex) {}
	}

	@Override
	public void setAdditionalJavaClassPath(String[] paths) {
		final StringBuilder builder = new StringBuilder();
		if (paths.length > 0) {
			builder.append(paths[0]);
		}
		for (int i = 1; i < paths.length; ++i) {
			builder.append(';');
			builder.append(paths[i]);
		}
		try {
			project.setPersistentProperty(javaClassPathID, builder.toString());
		} catch (final CoreException ex) {}
	}

	@Override
	public void setFSTModel(FSTModel model) {
		fstModel = model;
	}

	@Override
	public boolean buildRelevantChanges() {
		return buildRelevantChanges;
	}

	@Override
	public void built() {
		buildRelevantChanges = false;
	}

	@Override
	public String getContractComposition() {
		String contractComposition = null;
		final ProjectScope ps = new ProjectScope(project);
		final IEclipsePreferences prefs = ps.getNode("de.ovgu.featureide.core");
		contractComposition = prefs.get("contract", DEFAULT_CONTRACT_COMPOSITION);
		return contractComposition;
	}

	@Override
	public void setContractComposition(String contractComposition) {
		try {
			final ProjectScope ps = new ProjectScope(project);
			final IEclipsePreferences prefs = ps.getNode("de.ovgu.featureide.core");
			prefs.put("contract", contractComposition);
			prefs.flush();
		} catch (final BackingStoreException e) {
			LOGGER.logError(e);
		}
	}

	private static final QualifiedName META_PRODUCT_GENERATION =
		new QualifiedName(FeatureProject.class.getName() + "#MetaProductGeneration", FeatureProject.class.getName() + "#MetaProductGeneration");

	@Override
	public String getMetaProductGeneration() {
		String metaProductGeneration = null;
		try {
			metaProductGeneration = project.getPersistentProperty(META_PRODUCT_GENERATION);
		} catch (final CoreException e) {
			LOGGER.logError(e);
		}
		if (metaProductGeneration == null) {
			return META_THEOREM_PROVING;
		}
		return metaProductGeneration;
	}

	@Override
	public void setMetaProductGeneration(String metaProductGeneration) {
		try {
			project.setPersistentProperty(META_PRODUCT_GENERATION, metaProductGeneration);
		} catch (final CoreException e) {
			LOGGER.logError(e);
		}
	}

	@Override
	public String toString() {
		return project.getName();
	}

	@Override
	public String getCompositionMechanism() {
		String compositionMechanism = null;
		try {
			compositionMechanism = project.getPersistentProperty(compositionMechanismConfigID);
		} catch (final CoreException e) {
			LOGGER.logError(e);
		}
		if (compositionMechanism == null) {
			if (getComposer().getCompositionMechanisms().length != 0) {
				compositionMechanism = getComposer().getCompositionMechanisms()[0];
			} else {
				compositionMechanism = "";
			}
		}
		return compositionMechanism;
	}

	@Override
	public void setCompositionMechanism(String compositionMechanism) {
		try {
			project.setPersistentProperty(compositionMechanismConfigID, compositionMechanism);
		} catch (final CoreException e) {
			LOGGER.logError(e);
		}
	}

	@Override
	public Path getInternalConfigurationFile() {
		return getInternalConfigurationFile(currentConfiguration);
	}

	@Override
	public Path getInternalConfigurationFile(Path configurationFile) {
		final String fileName = "." + FileHandler.getFileName(configurationFile) + "." + FeatureIDEFormat.EXTENSION;
		final Path internalFile = configurationFile.getParent().resolve(fileName);

		return (Files.isReadable(internalFile)) ? internalFile : null;
	}

	@Override
	public IFeatureModelManager getFeatureModelManager() {
		return featureModelManager;
	}

	/**
	 * Checks for problems in feature model, configurations, feature coverage and feature folders
	 */
	@Override
	public void checkForProblems() {
		checkFeatureCoverage();
		checkConfigurations(getAllConfigurations());
		modelFile.deleteAllModelMarkers();
		for (final Problem warning : featureModelManager.getLastProblems()) {
			modelFile.createModelMarker(warning.message, warning.severity.getLevel(), warning.line);
		}
		if (!featureModelManager.getLastProblems().containsError()) {
			if (!featureModelManager.getPersistentFormula().getAnalyzer().isValid(null)) {
				modelFile.createModelMarker(THE_FEATURE_MODEL_IS_VOID_COMMA__I_E__COMMA__IT_CONTAINS_NO_PRODUCTS, IMarker.SEVERITY_ERROR, 0);
			}
		}
		try {
			createAndDeleteFeatureFolders();
		} catch (final CoreException e) {
			LOGGER.logError(e);
		}
	}

}
