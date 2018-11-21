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

	@CheckForNull
	public static FeatureModelManager getInstance(Path path) {
		return getInstance(path, true);
	}

	@CheckForNull
	public static final FeatureModelManager getInstance(Path identifier, boolean createInstance) {
		return getInstance(identifier, createInstance, FeatureModelManager.class);
	}

	public static final IFeatureModel load(Path path) {
		return FeatureModelIO.getInstance().load(path);
	}

	public static final boolean save(IFeatureModel featureModel, Path path, IPersistentFormat<IFeatureModel> format) {
		return FeatureModelIO.getInstance().save(featureModel, path, format);
	}

	protected FeatureModelManager(Path identifier) {
		super(identifier, FMFormatManager.getInstance(), FMFactoryManager.getInstance());
		variableObject.setSourceFile(identifier);
	}

	@Override
	public void overwrite() {
		persistentObject.setUndoContext(variableObject.getUndoContext());
		super.overwrite();
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

}
