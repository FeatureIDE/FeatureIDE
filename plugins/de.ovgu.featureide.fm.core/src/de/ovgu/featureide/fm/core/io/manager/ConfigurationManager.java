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
import javax.annotation.Nonnull;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.DefaultFormat;
import de.ovgu.featureide.fm.core.functional.Functional.ICriticalConsumer;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.ProblemList;

/**
 * Responsible to load and save all information for a feature model instance.
 *
 * @author Sebastian Krieter
 */
public class ConfigurationManager extends FileManager<Configuration> {

	private static class ObjectCreator extends FileManager.ObjectCreator<Configuration> {

		private final Path modelFile;

		public ObjectCreator(Path modelFile) {
			super();
			this.modelFile = modelFile;
		}

		@Override
		protected Configuration createObject() {
			final FeatureModelManager featureModelManager = FeatureModelManager.getInstance(modelFile);
			return new Configuration(featureModelManager.getObject());
		}

		@Override
		protected Snapshot<Configuration> createSnapshot(Configuration object) {
			return new Snapshot<>(object.clone());
		}
	}

	private static class ObjectCreator2 extends FileManager.ObjectCreator<Configuration> {

		private final IFeatureModel model;

		public ObjectCreator2(IFeatureModel model) {
			super();
			this.model = model;
		}

		@Override
		protected Configuration createObject() {
			return new Configuration(model);
		}

		@Override
		protected Snapshot<Configuration> createSnapshot(Configuration object) {
			return new Snapshot<>(object.clone());
		}
	}

	@Nonnull
	public static IPersistentFormat<Configuration> getDefaultFormat() {
		return new DefaultFormat();
	}

	@CheckForNull
	public static ConfigurationManager getInstance(Path path, Path modelFile) {
		return FileManager.getInstance(path, new ObjectCreator(modelFile), ConfigurationManager.class, ConfigFormatManager.getInstance());
	}

	@CheckForNull
	public static ConfigurationManager getInstance(Path path, IFeatureModel model) {
		return FileManager.getInstance(path, new ObjectCreator2(model), ConfigurationManager.class, ConfigFormatManager.getInstance());
	}

	public static FileHandler<Configuration> getFileHandler(Path configurationFile, Path modelFile) {
		return SimpleFileHandler.getFileHandler(configurationFile, new ObjectCreator(modelFile), ConfigFormatManager.getInstance());
	}

	public static FileHandler<Configuration> getFileHandler(Path configurationFile, IFeatureModel model) {
		return SimpleFileHandler.getFileHandler(configurationFile, new ObjectCreator2(model), ConfigFormatManager.getInstance());
	}

	public static Configuration load(Path configurationFile, Path modelFile) {
		return getFileHandler(configurationFile, modelFile).getObject();
	}

	public static Configuration load(Path configurationFile, Path modelFile, ProblemList problems) {
		final FileHandler<Configuration> fileHandler = getFileHandler(configurationFile, modelFile);
		problems.addAll(fileHandler.getLastProblems());
		return fileHandler.getObject();
	}

	public static Configuration load(Path configurationFile, IFeatureModel model) {
		return getFileHandler(configurationFile, model).getObject();
	}

	public static Configuration load(Path configurationFile, IFeatureModel model, ProblemList problems) {
		final FileHandler<Configuration> fileHandler = getFileHandler(configurationFile, model);
		problems.addAll(fileHandler.getLastProblems());
		return fileHandler.getObject();
	}

	public static boolean save(Configuration configuration, Path path, IPersistentFormat<Configuration> format) {
		return !SimpleFileHandler.save(path, configuration, format).containsError();
	}

	// TODO !!! react on feature name change
	private class FeatureModelChangeListner implements IEventListener {

		@Override
		public void propertyChange(FeatureIDEEvent evt) {
			final EventType eventType = evt.getEventType();
			switch (eventType) {
			case FEATURE_NAME_CHANGED:
				// TODO !!! react on feature name change
				// String oldName = (String) evt.getOldValue();
				// String newName = (String) evt.getNewValue();
				// FeatureModelManager.this.renameFeature((IFeatureModel) evt.getSource(), oldName, newName);
				break;
			case MODEL_DATA_OVERRIDDEN:
				// TODO !!! check correctness
				editObject().setFeatureModel(featureModelManager.getObject());
			default:
				break;
			}
		}
	}

	private FeatureModelManager featureModelManager;

	protected ConfigurationManager(SimpleFileHandler<Configuration> fileHandler, FileManager.ObjectCreator<Configuration> objectCreator) {
		super(fileHandler, objectCreator);

		featureModelManager.addListener(new FeatureModelChangeListner());
	}

	@Override
	public boolean externalSave(ICriticalConsumer<Configuration> externalSaveMethod) {
		return true;
	}

	public FeatureModelManager getFeatureModelManager() {
		return featureModelManager;
	}

}
