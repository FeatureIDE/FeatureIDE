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
package de.ovgu.featureide.fm.core.io.manager;

import javax.annotation.CheckForNull;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.velvet.VelvetFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelFormat;

/**
 * Responsible to load and save all information for a feature model instance.
 * 
 * @author Sebastian Krieter
 */
public class FeatureModelManager extends AFileManager<IFeatureModel> {

	public enum IOType {
		XML_FIDE(0), VELVET(1), VELVET_IMPORT(2);

		private final int index;

		private IOType(int index) {
			this.index = index;
		}

		public int getIndex() {
			return index;
		}
	}

	@CheckForNull
	public static IOType getTypeByFileName(String fileName) {
		if (fileName.endsWith(".xml")) {
			return IOType.XML_FIDE;
		} else if (fileName.endsWith(".velvet")) {
			return IOType.VELVET;
		}
		return null;
	}

	public static IPersistentFormat<IFeatureModel> getFormat(IOType ioType) {
		switch (ioType) {
		case VELVET:
			return new VelvetFeatureModelFormat();
		case VELVET_IMPORT:
			return new VelvetFeatureModelFormat();
		case XML_FIDE:
			return new XmlFeatureModelFormat();
		default:
			return null;
		}
	}

	public static FeatureModelManager getInstance(String absolutePath, IOType ioType) {
		return getInstance(absolutePath, getFormat(ioType));
	}

	public static FeatureModelManager getInstance(String absolutePath, IPersistentFormat<IFeatureModel> format) {
		final FeatureModelManager instance = FileManagerMap.getInstance(absolutePath, format, FeatureModelManager.class);
		instance.init();
		return instance;
	}

	protected FeatureModelManager(String absolutePath, IPersistentFormat<IFeatureModel> modelHandler) {
		super(absolutePath, modelHandler);
	}

	@Override
	protected IFeatureModel copyObject(IFeatureModel oldObject) {
		return oldObject.clone();
	}

	@Override
	protected IFeatureModel createNewObject() {
		final IFeatureModel model = FMFactoryManager.getFactory(getFormat().getFactoryID()).createFeatureModel();
		model.setSourceFile(path.toFile());
		return model;
	}

}
