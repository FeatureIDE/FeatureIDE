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
package de.ovgu.featureide.ahead;

import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.init.ILibrary;
import de.ovgu.featureide.fm.core.io.guidsl.GuidslFormat;

/**
 * The library object for the fm.core plug-in when using as a stand-alone library.
 *
 * @author Sebastian Krieter
 */
public final class AheadLibrary implements ILibrary {

	private static AheadLibrary instance;

	public static AheadLibrary getInstance() {
		if (instance == null) {
			instance = new AheadLibrary();
		}
		return instance;
	}

	private AheadLibrary() {}

	@Override
	public void install() {
		FMFormatManager.getInstance().addExtension(new GuidslFormat());
	}

	@Override
	public void uninstall() {}

}
