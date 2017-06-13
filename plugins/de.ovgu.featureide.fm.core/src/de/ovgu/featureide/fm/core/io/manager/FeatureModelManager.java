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

/**
 * Responsible to load and save all information for a feature model instance.
 * 
 * @author Sebastian Krieter
 */
public class FeatureModelManager extends AFileManager<IFeatureModel> {

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

	public static FeatureModelManager getInstance(IFeatureModel model, String absolutePath, IPersistentFormat<IFeatureModel> format) {
		final FeatureModelManager instance = FileManagerMap.getInstance(model, absolutePath, format, FeatureModelManager.class, IFeatureModel.class);
		model.setSourceFile(Paths.get(absolutePath));
		instance.read();
		return instance;
	}

	protected FeatureModelManager(IFeatureModel model, String absolutePath, IPersistentFormat<IFeatureModel> modelHandler) {
		super(model, absolutePath, modelHandler);
	}

	@Override
	protected IFeatureModel copyObject(IFeatureModel oldObject) {
		return oldObject.clone();
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

	@Override
	public boolean externalSave(Runnable externalSaveMethod) {
		return true;
	}

}
