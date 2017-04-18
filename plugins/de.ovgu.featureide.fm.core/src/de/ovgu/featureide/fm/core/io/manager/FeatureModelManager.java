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
import java.nio.file.Paths;

import javax.annotation.CheckForNull;

import de.ovgu.featureide.fm.core.ExtensionManager;
import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.InternalFeatureModelFormat;

/**
 * Responsible to load and save all information for a feature model instance.
 * 
 * @author Sebastian Krieter
 */
public class FeatureModelManager extends AFileManager<IFeatureModel> {

	/**
	 * Returns a singleton instance of a feature model manager associated with the specified model file.
	 * 
	 * @param modelFile Path to the physical model file.
	 * @return
	 */
	public static FeatureModelManager getInstance(Path modelFile) {
		final String path = modelFile.toAbsolutePath().toString();
		FeatureModelManager featureModelManager = FileManagerMap.<IFeatureModel, FeatureModelManager> getInstance(path);
		if (featureModelManager == null) {
			IFeatureModelFactory factory;
			final IFeatureModelFormat format = FeatureModelManager.getFormat(path);
			// TODO throw exception
			if (format == null) {
				Logger.logError(new ExtensionManager.NoSuchExtensionException("No format found for " + path));
				try {
					factory = FMFactoryManager.getDefaultFactoryForPath(path);
				} catch (Exception e) {
					Logger.logError(e);
					factory = FMFactoryManager.getDefaultFactory();
				}
			} else {
				try {
					factory = FMFactoryManager.getFactory(path, format);
				} catch (Exception e) {
					Logger.logError(e);
					factory = FMFactoryManager.getDefaultFactory();
				}
			}
			featureModelManager = FeatureModelManager.getInstance(factory.createFeatureModel(), path, format);
		}
		return featureModelManager;
	}

	@CheckForNull
	public static IFeatureModelFormat getFormat(String fileName) {
		return FMFormatManager.getInstance().getFormatByFileName(fileName);
	}

	@Override
	public IFeatureModelFormat getFormat() {
		return (IFeatureModelFormat) super.getFormat();
	}

	/**
	 * Returns a singleton instance of a feature model manager associated with the specified model file.
	 * 
	 * @param model
	 * @param absolutePath
	 * @param format
	 * @return
	 */
	public static FeatureModelManager getInstance(IFeatureModel model, String absolutePath, IPersistentFormat<IFeatureModel> format) {
		final FeatureModelManager instance = FileManagerMap.getInstance(model, absolutePath, format, FeatureModelManager.class, IFeatureModel.class);
		return instance;
	}

	protected FeatureModelManager(IFeatureModel model, String absolutePath, IPersistentFormat<IFeatureModel> modelHandler) {
		super(setSourcePath(model, absolutePath), absolutePath, modelHandler);
	}

	private static IFeatureModel setSourcePath(IFeatureModel model, String absolutePath) {
		model.setSourceFile(Paths.get(absolutePath));
		return model;
	}

	@Override
	protected boolean compareObjects(IFeatureModel o1, IFeatureModel o2) {
		final InternalFeatureModelFormat format = new InternalFeatureModelFormat();
		final String s1 = format.getInstance().write(o1);
		final String s2 = format.getInstance().write(o2);
		return s1.equals(s2);
	}

	@Override
	public void override() {
		localObject.setUndoContext(variableObject.getUndoContext());
		super.override();
	}

	@Override
	protected IFeatureModel copyObject(IFeatureModel oldObject) {
		final IFeatureModel clone = oldObject.clone();
		clone.setUndoContext(oldObject.getUndoContext());
		return clone;
	}

	public static IFeatureModel readFromFile(Path path) {
		try {
			final String pathString = path.toAbsolutePath().toString();
			final IFeatureModelFormat format = FMFormatManager.getInstance().getFormatByFileName(pathString);
			final IFeatureModel featureModel = FMFactoryManager.getFactory(pathString, format).createFeatureModel();
			FileHandler.load(path, featureModel, format);
			return featureModel;
		} catch (NoSuchExtensionException e) {
			Logger.logError(e);
		}
		return null;
	}

	public static boolean writeToFile(IFeatureModel featureModel, Path path) {
		final String pathString = path.toAbsolutePath().toString();
		final IFeatureModelFormat format = FMFormatManager.getInstance().getFormatByFileName(pathString);
		return !FileHandler.save(path, featureModel, format).containsError();
	}
	
	public static boolean convert(Path inPath, Path outPath) {
		IFeatureModel featureModel = readFromFile(inPath);
		if (featureModel == null) {
			return false;
		}
		return writeToFile(featureModel, outPath);
	}

}
