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
package de.ovgu.featureide.fm.ui.editors.elements;

import javax.annotation.CheckForNull;

import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.manager.AFileManager;
import de.ovgu.featureide.fm.core.io.manager.FileManagerMap;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * {@link AFileManager File manager} for {@link IGraphicalFeatureModel graphical feature model} representation.
 * 
 * @author Sebastian Krieter
 */
public class GraphicalFeatureModelManager extends AFileManager<IGraphicalFeatureModel> {

	@CheckForNull
	public static IPersistentFormat<IGraphicalFeatureModel> getFormat(String fileName) {
		return new GraphicalFeatureModelFormat();
	}

	public static GraphicalFeatureModelManager getInstance(IGraphicalFeatureModel model, String absolutePath, IPersistentFormat<IGraphicalFeatureModel> format) {
		final GraphicalFeatureModelManager manager = FileManagerMap.getInstance(model, absolutePath, format, GraphicalFeatureModelManager.class, IGraphicalFeatureModel.class);
		manager.read();
		return manager;
	}

	protected GraphicalFeatureModelManager(IGraphicalFeatureModel model, String absolutePath, IPersistentFormat<IGraphicalFeatureModel> format) {
		super(model, absolutePath, format);
	}

	@Override
	protected IGraphicalFeatureModel copyObject(IGraphicalFeatureModel graphicalItem) {
		return graphicalItem.clone();
	}

	@Override
	public boolean externalSave(Runnable externalSaveMethod) {
		return true;
	}

}
