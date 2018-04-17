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
package de.ovgu.featureide.fm.core.io.cnf;

import org.prop4j.Node;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.io.APersistentFormat;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.ProblemList;

/**
 * Reads / Writes feature models in the DIMACS CNF format.
 *
 * @author Sebastian Krieter
 */
public class CNFFormat extends APersistentFormat<IFeatureModel> implements IFeatureModelFormat {

	public static final String ID = PluginID.PLUGIN_ID + ".format.fm." + CNFFormat.class.getSimpleName();

	@Override
	public ProblemList read(IFeatureModel featureModel, CharSequence source) {
		throw new UnsupportedOperationException();
	}

	@Override
	public String write(IFeatureModel featureModel) {
		final Node nodes = AdvancedNodeCreator.createCNF(featureModel);
		final StringBuilder cnf = new StringBuilder();
		cnf.append("Logical Symbols:\r\n");
		cnf.append(nodes.toString(NodeWriter.logicalSymbols));
		cnf.append("\r\n\r\nTextual Symbols:\r\n");
		cnf.append(nodes.toString(NodeWriter.textualSymbols));
		cnf.append("\r\n\r\nJava Symbols:\r\n");
		cnf.append(nodes.toString(NodeWriter.javaSymbols));
		cnf.append("\r\n\r\nShort Symbols:\r\n");
		cnf.append(nodes.toString(NodeWriter.shortSymbols));
		return cnf.toString();
	}

	@Override
	public String getSuffix() {
		return "txt";
	}

	@Override
	public CNFFormat getInstance() {
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
		return "CNF";
	}

}
