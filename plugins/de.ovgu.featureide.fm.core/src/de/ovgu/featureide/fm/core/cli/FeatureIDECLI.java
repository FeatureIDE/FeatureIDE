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

import java.io.PrintStream;
import java.util.Arrays;

import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
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
			System.err.println("No operation specified!");
			printHelp(System.err);
			return;
		}
		System.out.println(Arrays.asList(args));

		final String functionName = args[0];

		LibraryManager.registerLibrary(FMCoreLibrary.getInstance());

		ICLIFunction function = null;
		try {
			function = CLIFunctionManager.getInstance().getFactory(functionName);
		} catch (final NoSuchExtensionException e) {
			System.err.println("No function found with the name " + functionName);
			printHelp(System.err);
			return;
		}

		try {
			function.run(Arrays.asList(args).subList(1, args.length));
		} catch (final IllegalArgumentException e) {
			System.err.println(e.getMessage());
			System.err.println(function.getHelp());
			return;
		}
	}

	private static void printHelp(PrintStream printStream) {
		printStream.println("Following functions are available:");
		for (final ICLIFunction availableFunction : CLIFunctionManager.getInstance().getExtensions()) {
			printStream.println("\t" + availableFunction.getName());
		}
	}

}
