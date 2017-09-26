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
package de.ovgu.featureide.fm.core.base.impl;

import java.io.File;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;

import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * This is a helper class to realize unique numeric identifiers for feature models in respect to the models physical file. Each feature model is required to be
 * assigned to an unique identifier. This unique identifier is coupled to the model file, such that the file path determines the feature models identifier.
 *
 * @see IFeatureModel#setSourceFile(File)
 * @see FeatureModel#setSourceFile(File)
 *
 * @author Sebastian Krieter
 * @author Marcus Pinnecke (Feature Interface)
 */
public class ModelFileIdMap {

	private static final Map<String, Long> map = new HashMap<>();

	/**
	 * Returns the feature models unique numeric identifier which is determined by the feature models physical file. A call to this method returns the id
	 * associated with <b>modelFile</b> if the model identifier was already associated to this file name. Otherwise, the <b>featureModel</b>'s identifier is
	 * returned and associated to <b>modelFile</b> for further usage. <br/> <br/> <b>Note</b>: There is no check if <b>featureModel.getId()</b> is unequal to
	 * the identifier associated with <b>modelFile</b>, i.e., if there is already an identifier associated with <b>modelFile</b> which is unequal to
	 * <b>featureModel</b>'s model identifier, <b>modelFile</b>' identifier is returned.
	 *
	 * @param featureModel The feature model (might be <b>null</b>, if <b>modelFile</b> is associated to an identifier already)
	 * @param modelFile The key value for association of feature model unique numeric identifiers. Is intended to point to the feature models underlying model
	 *        (have to be <b>non-null</b>) physical file
	 * @return The identifier associated with <b>modelFile</b> if there is already such an association. </b>featureModel</b>'s identifier otherwise.
	 */
	public static synchronized long getModelId(IFeatureModel featureModel, Path modelFile) {
		final String fileLocation = modelFile.toAbsolutePath().toString();
		Long id = map.get(fileLocation);
		if (id == null) {
			id = featureModel.getId();
			map.put(fileLocation, id);
		}
		return id;
	}

}
