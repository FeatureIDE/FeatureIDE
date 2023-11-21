/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui;

import java.io.IOException;
import java.nio.file.Path;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;

import de.ovgu.featureide.fm.core.io.FileSystem;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.elements.TikzGraphicalFeatureModelFormat;

public class FMTikzExporter implements ExportType<GraphicalViewerImpl> {

	@Override
	public String getFileExtension() {
		return "tex";
	}

	@Override
	public String getDescription() {
		return "LaTeX-Document with TikZ";
	}

	@Override
	public void export(Path path, GraphicalViewerImpl object) throws IOException {
		// create new folder
		final Path exportDir = "tex".equals(SimpleFileHandler.getFileExtension(path)) ? path.resolveSibling(SimpleFileHandler.getFileName(path)) : path;

		FileSystem.mkDir(exportDir);

		final IGraphicalFeatureModel model = (IGraphicalFeatureModel) object.getContents().getModel();

		save(exportDir, "head.tex", new TikzGraphicalFeatureModelFormat.TikZHeadFormat(), model);
		save(exportDir, "body.tex", new TikzGraphicalFeatureModelFormat.TikZBodyFormat(path.getFileName().toString()), model);
		save(exportDir, path.getFileName().toString(), new TikzGraphicalFeatureModelFormat.TikZMainFormat(), model);
	}

	private void save(final Path exportDir, String fileName, IPersistentFormat<IGraphicalFeatureModel> format, IGraphicalFeatureModel model) {
		final ProblemList result = SimpleFileHandler.save(exportDir.resolve(fileName), model, format).getErrors();
		if (!result.isEmpty()) {
			final Problem problem = result.get(0);
			throw problem.error != null //
				? new RuntimeException(problem.error) //
				: new RuntimeException(problem.getMessage());
		}
	}

}
