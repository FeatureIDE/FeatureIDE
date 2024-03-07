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
package de.ovgu.featureide.fm.ui.editors.configuration;

import java.io.IOException;
import java.nio.file.Path;

import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.FileSystem;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;
import de.ovgu.featureide.fm.ui.ExportType;

/**
 * Exports a tikz representation of a configuration.
 *
 * @author Sebastian Krieter
 */
public class ConfigurationTikzExporter implements ExportType<Configuration> {

	@Override
	public String getFileExtension() {
		return "tex";
	}

	@Override
	public String getDescription() {
		return "LaTeX-Document with TikZ";
	}

	@Override
	public void export(Path path, Configuration object) throws IOException {
		final Path exportDir = "tex".equals(SimpleFileHandler.getFileExtension(path)) ? path.resolveSibling(SimpleFileHandler.getFileName(path)) : path;

		FileSystem.mkDir(exportDir);

		save(exportDir, "head.tex", new LatexFormat.LaTeXHead(), null);
		save(exportDir, "body.tex", new LatexFormat.LaTeXBody(path.getFileName().toString()), null);
		save(exportDir, path.getFileName().toString(), new LatexFormat.LaTeXMain(), object);
	}

	private void save(final Path exportDir, String fileName, IPersistentFormat<Configuration> format, Configuration model) {
		final ProblemList result = SimpleFileHandler.save(exportDir.resolve(fileName), model, format).getErrors();
		if (!result.isEmpty()) {
			final Problem problem = result.get(0);
			throw problem.error != null //
				? new RuntimeException(problem.error) //
				: new RuntimeException(problem.getMessage());
		}
	}

}
