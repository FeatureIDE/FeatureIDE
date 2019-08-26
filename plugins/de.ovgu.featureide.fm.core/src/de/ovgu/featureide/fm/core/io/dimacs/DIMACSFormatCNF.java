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
package de.ovgu.featureide.fm.core.io.dimacs;

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.io.APersistentFormat;

/**
 * Reads and writes feature models in the DIMACS CNF format.
 *
 * @author Sebastian Krieter
 * @author Timo G&uuml;nther
 */
public class DIMACSFormatCNF extends APersistentFormat<CNF> {

	public static final String ID = PluginID.PLUGIN_ID + ".format.cnf." + DIMACSFormatCNF.class.getSimpleName();

	@Override
	public String write(CNF cnf) {
		final DimacsWriter w = new DimacsWriter(cnf);
		w.setWritingVariableDirectory(true);
		return w.write();
	}

	@Override
	public String getSuffix() {
		return "dimacs";
	}

	@Override
	public DIMACSFormatCNF getInstance() {
		return this;
	}

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public boolean supportsWrite() {
		return true;
	}

	@Override
	public String getName() {
		return "DIMACS";
	}

}
