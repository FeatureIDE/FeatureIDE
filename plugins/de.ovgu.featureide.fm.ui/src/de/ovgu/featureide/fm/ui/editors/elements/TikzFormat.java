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

import de.ovgu.featureide.fm.core.io.APersistentFormat;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Converts the Feature Model Diagram in a tex-format using tikz.
 *
 * @author Simon Wenk
 * @author Yang Liu
 */
public class TikzFormat extends APersistentFormat<IGraphicalFeatureModel> {

	// public static final String ID = PluginID.PLUGIN_ID + ".format.fm." + TikzFormat.class.getSimpleName();
	public static final String ID = "de.ovgu.featureide.tikzformat";

	@Override
	public String write(IGraphicalFeatureModel object) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean supportsRead() {
		return false;

	}

	@Override
	public boolean supportsWrite() {
		return true;

	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.io.IPersistentFormat#getSuffix()
	 */
	@Override
	public String getSuffix() {
		return ".tex";
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.io.IPersistentFormat#getName()
	 */
	@Override
	public String getName() {
		return "FeatureIDE";
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.IExtension#getId()
	 */
	@Override
	public String getId() {
		// TODO Auto-generated method stub
		return ID;
	}

}
