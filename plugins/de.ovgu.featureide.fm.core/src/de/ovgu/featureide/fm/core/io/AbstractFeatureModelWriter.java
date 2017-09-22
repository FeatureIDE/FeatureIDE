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
package de.ovgu.featureide.fm.core.io;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;

/**
 * Default reader to be extended for each feature model format.
 *
 * If IFile support is needed, the {@link FeatureModelReaderIFileWrapper} has to be used.
 *
 * @deprecated Use {@link IFeatureModelFormat} and {@link FileHandler} instead.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke (Feature Interface)
 */
@Deprecated
public abstract class AbstractFeatureModelWriter extends AbstractObjectWriter<IFeatureModel> implements IFeatureModelWriter {

	@Override
	public IFeatureModel getFeatureModel() {
		return getObject();
	}

	@Override
	public void setFeatureModel(IFeatureModel featureModel) {
		setObject(featureModel);
	}

}
