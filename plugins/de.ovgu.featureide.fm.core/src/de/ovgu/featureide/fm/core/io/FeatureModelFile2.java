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
package de.ovgu.featureide.fm.core.io;

import java.io.FileNotFoundException;
import java.util.HashMap;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * Ensures that the same {@code FeatureModel} instance is used when loading a model file.
 * 
 * @author Sebastian Krieter
 */
public class FeatureModelFile2 {
	
	private static final HashMap<String, FeatureModelFile2> map = new HashMap<>();
	
	public static final FeatureModelFile2 getInstance(IFile file) {
		final String key = file.getProject().getLocation().toString();
		FeatureModelFile2 featureModelFile = map.get(key);
		if (featureModelFile == null) {
			featureModelFile = new FeatureModelFile2(file);
			map.put(key, featureModelFile);
		}
		return featureModelFile;
	}
	
	private final FeatureModel featureModel;
	private final IFile modelFile;

	private FeatureModelFile2(IFile modelFile) {
		this.modelFile = modelFile;
		
		final int modelType = ModelIOFactory.getTypeByFileName(modelFile.getName());
		final FeatureModel newFeatureModel = ModelIOFactory.getNewFeatureModel(modelType);
		if (newFeatureModel != null) {
			final FeatureModelReaderIFileWrapper modelReader = new FeatureModelReaderIFileWrapper(ModelIOFactory.getModelReader(newFeatureModel, modelType));
			try {
				modelReader.readFromFile(modelFile);
			} catch (FileNotFoundException | UnsupportedModelException e) {
				FMCorePlugin.getDefault().logError(e);
			}
			featureModel = modelReader.getFeatureModel();
		} else {
			featureModel = new FeatureModel();
		}
	}

	public FeatureModel getFeatureModel() {
		return featureModel;
	}

	public IFile getModelFile() {
		return modelFile;
	}
	
}
