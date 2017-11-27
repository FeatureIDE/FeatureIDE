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

import de.ovgu.featureide.fm.core.base.impl.FormatManager;
import de.ovgu.featureide.fm.core.functional.Functional.ICriticalConsumer;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.manager.FileManager;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;
import de.ovgu.featureide.fm.core.io.manager.Snapshot;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * {@link FileManager File manager} for {@link IGraphicalFeatureModel graphical feature model} representation.
 *
 * @deprecated Use fileHandler instead. This class is of little use for {@link IGraphicalFeatureModel} as has not an dedicated editor. Will be removed.
 * @author Sebastian Krieter
 */
@Deprecated
public class GraphicalFeatureModelManager extends FileManager<IGraphicalFeatureModel> {

	private static class ObjectCreator extends FileManager.ObjectCreator<IGraphicalFeatureModel> {

		private final IGraphicalFeatureModel model;

		public ObjectCreator(IGraphicalFeatureModel model) {
			super();
			this.model = model;
		}

		@Override
		protected IGraphicalFeatureModel createObject() {
			return model;
		}

		@Override
		protected Snapshot<IGraphicalFeatureModel> createSnapshot(IGraphicalFeatureModel object) {
			return new Snapshot<>(object.clone());
		}
	}

	@CheckForNull
	public static GraphicalFeatureModelManager getInstance(Path path, IGraphicalFeatureModel model) {
		return FileManager.getInstance(path, new ObjectCreator(model), GraphicalFeatureModelManager.class,
				new FormatManager<GraphicalFeatureModelFormat>(GraphicalFeatureModelFormat.class));
	}

	public static IGraphicalFeatureModel load(Path path, IGraphicalFeatureModel model) {
		final GraphicalFeatureModelManager instance = getInstance(path, model);
		return instance.getObject();
	}

	public static IGraphicalFeatureModel load(Path path, IGraphicalFeatureModel model, ProblemList problems) {
		final GraphicalFeatureModelManager instance = getInstance(path, model);
		problems.addAll(instance.getLastProblems());
		return instance.getObject();
	}

	protected GraphicalFeatureModelManager(SimpleFileHandler<IGraphicalFeatureModel> fileHndler, ObjectCreator objectCreator) {
		super(fileHndler, objectCreator);
	}

	@Override
	public boolean externalSave(ICriticalConsumer<IGraphicalFeatureModel> externalSaveMethod) {
		return true;
	}

}
