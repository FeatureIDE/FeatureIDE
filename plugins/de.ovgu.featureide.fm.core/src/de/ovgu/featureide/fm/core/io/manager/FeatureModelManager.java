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

import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;

/**
 * Responsible to load and save all information for a feature model instance.
 *
 * @author Sebastian Krieter
 */
public class FeatureModelManager extends AFileManager<IFeatureModel> {

	private static final ObjectCreator<IFeatureModel> objectCreator =
		new ObjectCreator<IFeatureModel>(IFeatureModel.class, FeatureModelManager.class, FMFormatManager.getInstance()) {

			@Override
			protected IFeatureModel createObject(Path path, IPersistentFormat<IFeatureModel> format) throws NoSuchExtensionException {
				final IFeatureModel featureModel = FMFactoryManager.getFactory(path.toAbsolutePath().toString(), format).createFeatureModel();
				featureModel.setSourceFile(path);
				return featureModel;
			}
		};

	/**
	 * Returns an instance of a {@link IFileManager} for a certain file. Creates a new instance if none is available (Equivalent to calling
	 * {@link #getInstance(Path, boolean) getInstance(path, true)}).
	 *
	 * @param path The path pointing to the file.
	 *
	 * @return The manager instance for the specified file, or {@code null} if no instance was created yet.
	 *
	 * @throws ClassCastException When the found instance is no subclass of R.
	 */
	@CheckForNull
	public static FeatureModelManager getInstance(Path path) {
		return getInstance(path, true);
	}

	/**
	 * Returns an instance of a {@link IFileManager} for a certain file.
	 *
	 * @param createInstance Whether a new instance should be created, if none is available.
	 *
	 * @param path The path pointing to the file.
	 *
	 * @return The manager instance for the specified file, or {@code null} if no instance was created yet.
	 *
	 * @throws ClassCastException When the found instance is no subclass of R.
	 */
	@CheckForNull
	public static FeatureModelManager getInstance(Path path, boolean createInstance) {
		return (FeatureModelManager) AFileManager.getInstance(path, objectCreator, createInstance);
	}

	public static boolean save(IFeatureModel featureModel, Path path, IFeatureModelFormat format) {
		return !SimpleFileHandler.save(path, featureModel, format).containsError();
	}

	public static boolean convert(Path inPath, Path outPath, IFeatureModelFormat format) {
		final IFeatureModel featureModel = load(inPath).getObject();
		if (featureModel == null) {
			return false;
		}
		return save(featureModel, outPath, format);
	}

	protected FeatureModelManager(IFeatureModel model, FileIdentifier<IFeatureModel> identifier) {
		super(setSourcePath(model, identifier.getPath()), identifier);
	}

	private static IFeatureModel setSourcePath(IFeatureModel model, Path path) {
		model.setSourceFile(path);
		return model;
	}

	@Override
	public void override() {
		persistentObject.setUndoContext(variableObject.getUndoContext());
		super.override();
	}

	@Override
	public IFeatureModelFormat getFormat() {
		return (IFeatureModelFormat) super.getFormat();
	}

	@Override
	protected IFeatureModel copyObject(IFeatureModel oldObject) {
		final IFeatureModel clone = oldObject.clone();
		clone.setUndoContext(oldObject.getUndoContext());
		return clone;
	}

	public static FileHandler<IFeatureModel> load(Path path) {
		return getFileHandler(path, objectCreator);
	}

}
