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
package de.ovgu.featureide.fm.core.io.manager;

import java.nio.file.Path;

import javax.annotation.CheckForNull;

import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzerVar;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationPropagator;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.InternalFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.ProblemList;

/**
 * Responsible to load and save all information for a feature model instance.
 *
 * @author Sebastian Krieter
 */
public class FeatureModelManager extends FileManager<IFeatureModel> {

	public static class FeatureModelSnapshot extends Snapshot<IFeatureModel> {

		private final FeatureModelFormula formula;
		private final FeatureModelAnalyzer analyzer;

		public FeatureModelSnapshot(IFeatureModel featureModel) {
			super(featureModel);

			formula = new FeatureModelFormula(featureModel);
			analyzer = new FeatureModelAnalyzer(formula);
		}

		public FeatureModelFormula getFormula() {
			return formula;
		}

		public FeatureModelAnalyzer getAnalyzer() {
			return analyzer;
		}

		public ConfigurationPropagator getPropagator() {
			return new ConfigurationPropagator(formula, new Configuration(object));
		}

		public ConfigurationPropagator getPropagator(Configuration configuration) {
			return new ConfigurationPropagator(formula, configuration);
		}

		public ConfigurationPropagator getPropagator(Configuration configuration, boolean includeAbstract) {
			return new ConfigurationPropagator(formula, configuration, includeAbstract);
		}

		public ConfigurationPropagator getPropagator(boolean includeAbstract) {
			return new ConfigurationPropagator(formula, new Configuration(object), includeAbstract);
		}

	}

	/**
	 * Listens to feature model changes. Resets its formula if necessary.
	 */
	private class FeatureModelChangeListner implements IEventListener {

		@Override
		public void propertyChange(FeatureIDEEvent evt) {
			final EventType eventType = evt.getEventType();
			switch (eventType) {
			case ALL_FEATURES_CHANGED_NAME_TYPE: // Required because feature names are used as variable names.
			case CHILDREN_CHANGED:
			case CONSTRAINT_ADD:
			case CONSTRAINT_DELETE:
			case CONSTRAINT_MODIFY:
			case FEATURE_ADD:
			case FEATURE_ADD_ABOVE:
			case FEATURE_DELETE:
			case FEATURE_MODIFY: // TODO If a formula reset is required for this event type, remove this comment. Otherwise, remove this case.
			case FEATURE_NAME_CHANGED: // Required because feature names are used as variable names.
			case GROUP_TYPE_CHANGED:
			case HIDDEN_CHANGED: // TODO If a formula reset is required for this event type, remove this comment. Otherwise, remove this case.
			case MANDATORY_CHANGED:
			case MODEL_DATA_CHANGED:
			case MODEL_DATA_OVERRIDDEN:
			case PARENT_CHANGED:
			case STRUCTURE_CHANGED:
				break;
			default:
				break;
			}
		}
	}

	private static final ObjectCreator<IFeatureModel> objectCreator = new ObjectCreator<IFeatureModel>() {

		private IFeatureModelFactory factory = null;

		@Override
		protected void setPath(Path path, IPersistentFormat<IFeatureModel> format) throws Exception {
			super.setPath(path, format);
			factory = FMFactoryManager.getFactory(path.toAbsolutePath().toString(), format);
		}

		@Override
		protected IFeatureModel createObject() {
			final IFeatureModel featureModel = factory.createFeatureModel();
			featureModel.setSourceFile(path);
			return featureModel;
		}

		@Override
		protected Snapshot<IFeatureModel> createSnapshot(IFeatureModel object) {
			final IFeatureModel clone = object.clone();
			clone.setUndoContext(object.getUndoContext());
			return new FeatureModelSnapshot(clone);
		}

		@Override
		protected boolean compareObjects(IFeatureModel o1, IFeatureModel o2) {
			final InternalFeatureModelFormat format = new InternalFeatureModelFormat();
			final String s1 = format.getInstance().write(o1);
			final String s2 = format.getInstance().write(o2);
			return s1.equals(s2);
		}

	};

	/**
	 * Returns an instance of a {@link IFileManager} for a certain file.
	 *
	 * @param path The path pointing to the file.
	 *
	 * @return The manager instance for the specified file, or {@code null} if no instance was created yet.
	 *
	 * @throws ClassCastException When the found instance is no subclass of R.
	 */
	@CheckForNull
	public static FeatureModelManager getInstance(Path absolutePath) {
		return (FeatureModelManager) FileManager.getInstance(absolutePath, objectCreator, FeatureModelManager.class, FMFormatManager.getInstance());
	}

	@Deprecated
	@CheckForNull
	public static FeatureModelManager getInstance(IFeatureModel featureModel) {
		final Path sourceFile = featureModel.getSourceFile();
		if (sourceFile != null) {
			return getInstance(sourceFile);
		}
		return null;
	}

	public static IFeatureModel load(Path path) {
		final FeatureModelManager instance = getInstance(path);
		return instance.getObject();
	}

	public static IFeatureModel load(Path path, ProblemList problems) {
		final FeatureModelManager instance = getInstance(path);
		problems.addAll(instance.getLastProblems());
		return instance.getObject();
	}

	public static IFeatureModelFormat getFormat(String fileName) {
		return FMFormatManager.getInstance().getFormatByFileName(fileName);
	}

	public static boolean save(IFeatureModel featureModel, Path path) {
		final String pathString = path.toAbsolutePath().toString();
		final IFeatureModelFormat format = FMFormatManager.getInstance().getFormatByFileName(pathString);
		return !SimpleFileHandler.save(path, featureModel, format).containsError();
	}

	public static boolean convert(Path inPath, Path outPath) {
		final IFeatureModel featureModel = load(inPath);
		if (featureModel == null) {
			return false;
		}
		return save(featureModel, outPath);
	}

	@Deprecated
	public static ConfigurationPropagator getPropagator(Configuration configuration, boolean includeAbstractFeatures) {
		return new ConfigurationPropagator(configuration, includeAbstractFeatures);
	}

	@Deprecated
	public static ConfigurationPropagator getPropagator(IFeatureModel featureModel, boolean includeAbstractFeatures) {
		final Configuration configuration = new Configuration(featureModel);
		return new ConfigurationPropagator(configuration, includeAbstractFeatures);
	}

	protected FeatureModelManager(SimpleFileHandler<IFeatureModel> fileHandler, ObjectCreator<IFeatureModel> objectCreator) {
		super(fileHandler, objectCreator);

		variableObject.setSourceFile(path);
		persistentObject.getObject().setSourceFile(path);

		addListener(new FeatureModelChangeListner());

		// TODO !!! Rename manager method save -> write
		// TODO !!! Implement analyses for configurations
	}

	@Override
	protected void copyPropertiesOnOverride() {
		for (final IEventListener listener : variableObject.getListenerList()) {
			lastReadObject.addListener(listener);
		}
		lastReadObject.setUndoContext(variableObject.getUndoContext());
		persistentObject.getObject().setUndoContext(variableObject.getUndoContext());
	}

	@Override
	public IFeatureModelFormat getFormat() {
		return (IFeatureModelFormat) super.getFormat();
	}

	@Override
	public FeatureModelSnapshot getSnapshot() {
		return (FeatureModelSnapshot) super.getSnapshot();
	}

	public FeatureModelAnalyzerVar getVarAnalyzer() {
		return new FeatureModelAnalyzerVar(new FeatureModelFormula(editObject()));
	}

	@Deprecated
	public static FeatureModelAnalyzer getAnalyzer(IFeatureModel featureModel) {
		final FeatureModelManager instance = getInstance(featureModel);
		return instance == null ? new FeatureModelAnalyzer(new FeatureModelFormula(featureModel)) : instance.getSnapshot().getAnalyzer();
	}

}
