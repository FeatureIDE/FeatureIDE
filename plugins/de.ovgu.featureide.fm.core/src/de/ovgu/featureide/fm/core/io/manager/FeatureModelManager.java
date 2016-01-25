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

import java.io.File;

import javax.annotation.CheckForNull;

import org.eclipse.core.resources.IResource;

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

	private static enum FormatType implements IFormatType<IFeatureModel> {
		XML_FIDE("xml", XmlFeatureModelFormat.class),
		VELVET("velvet", VelvetFeatureModelFormat.class),
		FIDECONF("velvet", VelvetFeatureModelFormat.class);

		private final String suffix;
		private final Class<? extends IPersistentFormat<IFeatureModel>> format;

		private FormatType(String suffix, Class<? extends IPersistentFormat<IFeatureModel>> format) {
			this.suffix = suffix;
			this.format = format;
		}

		@Override
		public String getSuffix() {
			return suffix;
		}

		@Override
		public Class<? extends IPersistentFormat<IFeatureModel>> getFormat() {
			return format;
		}
	}

	public static FeatureModelManager getInstance(IResource modelFile) {
		final String path = modelFile.getLocation().toString();
		FeatureModelManager featureModelManager = FileManagerMap.<IFeatureModel, FeatureModelManager>getInstance(path);
		if (featureModelManager == null) {
			final IPersistentFormat<IFeatureModel> format = FeatureModelManager.getFormat(path);
			IFeatureModel featureModel = FMFactoryManager.getFactory(format.getFactoryID()).createFeatureModel();
			featureModelManager = FeatureModelManager.getInstance(featureModel, path, format);
		}
		return featureModelManager;
	}

	@CheckForNull
	public static IPersistentFormat<IFeatureModel> getFormat(String fileName) {
		return AFileManager.<IFeatureModel>getFormat(fileName, FormatType.values());
	}

	public static FeatureModelManager getInstance(IFeatureModel model, String absolutePath, IPersistentFormat<IFeatureModel> format) {
		final FeatureModelManager instance = FileManagerMap.getInstance(model, absolutePath, format, FeatureModelManager.class, IFeatureModel.class);
		model.setSourceFile(new File(absolutePath));
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

	private Object undoContext = null;

	public Object getUndoContext() {
		return undoContext;
	}

	public void setUndoContext(Object undoContext) {
		this.undoContext = undoContext;
	}

}
