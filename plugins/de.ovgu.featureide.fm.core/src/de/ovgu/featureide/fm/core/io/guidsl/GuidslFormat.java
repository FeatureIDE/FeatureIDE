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
package de.ovgu.featureide.fm.core.io.guidsl;

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.AFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * Reads / Writes feature models in the Guidsl format.
 *
 * @author Sebastian Krieter
 */
public class GuidslFormat extends AFeatureModelFormat {

	public static final String ID = PluginID.PLUGIN_ID + ".format.fm." + GuidslFormat.class.getSimpleName();
	public static final String FILE_EXTENSION = "m";

	@Override
	public ProblemList read(IFeatureModel featureModel, CharSequence source) {
		final ProblemList problemList = new ProblemList();
		final GuidslReader guidslReader = new GuidslReader();
		try {
			guidslReader.parseInputStream(featureModel, source.toString());
		} catch (final UnsupportedModelException e) {
			problemList.add(new Problem(e, e.lineNumber));
		}
		problemList.addAll(guidslReader.getWarnings());
		return problemList;
	}

	@Override
	public String write(IFeatureModel featureModel) {
		return new GuidslWriter().writeToString(featureModel);
	}

	@Override
	public String getSuffix() {
		return FILE_EXTENSION;
	}

	@Override
	public GuidslFormat getInstance() {
		return this;
	}

	@Override
	public boolean supportsRead() {
		return true;
	}

	@Override
	public boolean supportsWrite() {
		return true;
	}

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public String getName() {
		return "Guidsl";
	}

}
