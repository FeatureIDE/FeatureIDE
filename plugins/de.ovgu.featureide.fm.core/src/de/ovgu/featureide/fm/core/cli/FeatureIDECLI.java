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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import de.ovgu.featureide.fm.core.init.FMCoreLibrary;
import de.ovgu.featureide.fm.core.init.LibraryManager;

/**
 * Command line interface for several functions of FeatureIDE.
 *
 * @author Sebastian Krieter
 */
public class FeatureIDECLI {

	public static void main(String[] args) {
		if (args.length == 0) {
			System.out.println("No operation specified!");
		}
		System.out.println(Arrays.asList(args));

		LibraryManager.registerLibrary(FMCoreLibrary.getInstance());

		final List<ICLIFunction> functions = new ArrayList<>();
		functions.add(new ConfigurationGenerator());

		final String functionName = args[0];
		for (final ICLIFunction function : functions) {
			if (functionName.equals(function.getName())) {
				function.run(Arrays.asList(args).subList(1, args.length));
			}
		}

	}

}
