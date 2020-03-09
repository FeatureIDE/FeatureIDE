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
package de.ovgu.featureide.fm.core.cli;

import de.ovgu.featureide.fm.core.ExtensionManager;

/**
 * Manages all factories for configuration objects.
 *
 * @author Sebastian Krieter
 */
public class CLIFunctionManager extends ExtensionManager<ICLIFunction> {

	private static CLIFunctionManager instance = new CLIFunctionManager();

	public static CLIFunctionManager getInstance() {
		return instance;
	}

	@Override
	public boolean addExtension(ICLIFunction extension) {
		return (extension instanceof ICLIFunction) ? super.addExtension(extension) : false;
	}

	/**
	 * Returns a specific function associated with the string <b>id</b>.
	 *
	 * @param id the (unique) identifier for an instance of {@link ICLIFunction} to be returned
	 * @return An instance of the function associated with <b>id</b>, or throws a NoSuchExtensionException in case <b>id</b> is not associated with any
	 *         function.
	 * @throws NoSuchExtensionException If no factory with the given ID is registered.
	 */
	public ICLIFunction getFactory(String id) throws NoSuchExtensionException {
		return getExtension(id);
	}

}
