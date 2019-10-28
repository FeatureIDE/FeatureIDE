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
package de.ovgu.featureide.fm.core.analysis.cnf.solver;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.io.dimacs.DimacsWriter;

/**
 * TODO description
 *
 * @author Chico Sundermann
 */
public abstract class AExecutableSolver {

	protected final static String DIMACS_TEMP_PATH = "temp.dimacs";
	private final CNF cnf;

	public AExecutableSolver(CNF cnf) {
		this.cnf = cnf;
	}

	protected void createTemporaryDimacs() {
		// clear if one exists
		deleteTemporaryDimacs();
		final DimacsWriter dWriter = new DimacsWriter(cnf);
		final String dimacsContent = dWriter.write();
		writeToFile(DIMACS_TEMP_PATH, dimacsContent);
	}

	protected void deleteTemporaryDimacs() {
		final File dimacs = new File(DIMACS_TEMP_PATH);
		try {
			Files.deleteIfExists(dimacs.toPath());
		} catch (final IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	private static void writeToFile(String path, String content) {
		try {
			final BufferedWriter writer = new BufferedWriter(new FileWriter(path));
			writer.write(content);
			writer.close();
		} catch (final IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	public static String runBinary(String command) {
		final Runtime rt = Runtime.getRuntime();
		try {
			final Process ps = rt.exec(command);
			final java.io.InputStream is = ps.getInputStream();
			final java.util.Scanner s = new java.util.Scanner(is).useDelimiter("\\A");
			String val = "";
			if (s.hasNext()) {
				val = s.next();
			} else {
				val = "";
			}
			return val;
		} catch (final IOException e) {
			e.printStackTrace();
			return null;
		}
	}

	protected abstract Object parseResult(String result);

	public abstract Object execute();

	protected abstract String buildCommand();
}
