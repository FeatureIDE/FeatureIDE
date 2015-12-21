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
package de.ovgu.featureide.fm.ui.editors.elements;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
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

	public enum IOType {
		XML_FIDE(0);

		private final int index;

		private IOType(int index) {
			this.index = index;
		}

		public int getIndex() {
			return index;
		}
	}

	public static IPersistentFormat<IGraphicalFeatureModel> getFormat(IOType ioType) {
		switch (ioType) {
		case XML_FIDE:
			return new GraphicalFeatureModelFormat();
		default:
			return null;
		}
	}

	private IFeatureModel featureModel;

	public static GraphicalFeatureModelManager getInstance(String absolutePath, IOType ioType, IFeatureModel featureModel) {
		return getInstance(absolutePath, getFormat(ioType), featureModel);
	}
	
	public static GraphicalFeatureModelManager getInstance(String absolutePath, IPersistentFormat<IGraphicalFeatureModel> format, IFeatureModel featureModel) {
		final GraphicalFeatureModelManager manager = FileManagerMap.getInstance(absolutePath, format, GraphicalFeatureModelManager.class);
		if (manager.featureModel == null) {
			manager.featureModel = featureModel;
		}
		manager.init();
		return manager;
	}

	protected GraphicalFeatureModelManager(String absolutePath, IPersistentFormat<IGraphicalFeatureModel> format) {
		super(absolutePath, format);
	}

	@Override
	protected IGraphicalFeatureModel createNewObject() {
		// TODO _interfaces: implement factory for graphical feature model
		GraphicalFeatureModel graphicalItem = new GraphicalFeatureModel(featureModel);
		graphicalItem.init();
		return graphicalItem;
	}

	@Override
	protected IGraphicalFeatureModel copyObject(IGraphicalFeatureModel graphicalItem) {
		return graphicalItem.clone();
	}

}
