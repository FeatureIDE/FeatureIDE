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
package de.ovgu.featureide.fm.ui.editors.elements;

import java.nio.file.Path;

import javax.annotation.CheckForNull;

import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.base.impl.FormatManager;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.manager.AFileManager;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * {@link AFileManager File manager} for {@link IGraphicalFeatureModel graphical feature model} representation.
 *
 * @author Sebastian Krieter
 */
public class GraphicalFeatureModelManager extends AFileManager<IGraphicalFeatureModel> {

	private static class ObjectCreator extends AFileManager.ObjectCreator<IGraphicalFeatureModel> {

		private final IGraphicalFeatureModel model;

		public ObjectCreator(IGraphicalFeatureModel model) {
			super(IGraphicalFeatureModel.class, GraphicalFeatureModelManager.class,
					new FormatManager<GraphicalFeatureModelFormat>(GraphicalFeatureModelFormat.class));
			this.model = model;
		}

		@Override
		protected IGraphicalFeatureModel createObject(Path path, IPersistentFormat<IGraphicalFeatureModel> format) throws NoSuchExtensionException {
			return model;
		}
	}

	@CheckForNull
	public static GraphicalFeatureModelManager getInstance(Path path) {
		return AFileManager.getInstance(path, new ObjectCreator(null), false);
	}

	@CheckForNull
	public static GraphicalFeatureModelManager getInstance(Path path, IGraphicalFeatureModel model) {
		return AFileManager.getInstance(path, new ObjectCreator(model), true);
	}

	public static FileHandler<IGraphicalFeatureModel> load(Path path, IGraphicalFeatureModel model) {
		return getFileHandler(path, new ObjectCreator(model));
	}

	protected GraphicalFeatureModelManager(IGraphicalFeatureModel model, FileIdentifier<IGraphicalFeatureModel> identifier) {
		super(model, identifier);
	}

	@Override
	protected IGraphicalFeatureModel copyObject(IGraphicalFeatureModel graphicalItem) {
		return graphicalItem.clone();
	}

}
