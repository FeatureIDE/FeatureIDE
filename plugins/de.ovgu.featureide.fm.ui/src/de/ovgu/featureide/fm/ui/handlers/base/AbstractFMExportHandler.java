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
package de.ovgu.featureide.fm.ui.handlers.base;

import java.nio.file.Path;
import java.util.List;

import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.DefaultFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;

public abstract class AbstractFMExportHandler extends AbstractExportHandler<IFeatureModel> {

	@Override
	protected IFeatureModel getObject(Path path, IPersistentFormat<IFeatureModel> format) {
		IFeatureModelFactory factory;
		final FMFactoryManager factoryManager = FMFactoryManager.getInstance();
		try {
			factory = factoryManager.getFactory(path, format);
		} catch (final NoSuchExtensionException e) {
			Logger.logError(e);
			factory = DefaultFeatureModelFactory.getInstance();
		}
		return factory.create();
	}

	@Override
	protected IPersistentFormat<IFeatureModel> getInputFormat(Path path) {
		final List<IPersistentFormat<IFeatureModel>> formats = FMFormatManager.getInstance().getFormatListForExtension(path.getFileName());
		return formats.isEmpty() ? null : formats.get(0);
	}

}
