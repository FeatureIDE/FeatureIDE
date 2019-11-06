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

import java.math.BigInteger;
import java.nio.file.Paths;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.io.FileSystem;

/**
 *
 * @author Chico Sundermann
 */
public class CountAntomSolver extends AExecutableSolver {

	private final String binaryPathLinux;
	private final String binaryPathWindows;
	private final String binaryPathMac;

	private final int timeout;
	private final int numberOfThreads;
	private final int maxMemory;
	private final static String NUMBER_OF_THREADS_FLAG = "--noThreads=";
	private final static String MEMORY_SIZE_FLAG = "--memSize=";

	/**
	 * @param cnf
	 */
	public CountAntomSolver(CNF cnf, int timeout, int numberOfThreads, int maxMemory) {
		super(cnf);
		this.timeout = timeout;
		this.numberOfThreads = numberOfThreads;
		this.maxMemory = maxMemory;
		binaryPathLinux = FileSystem.getLib(Paths.get("lib/countAntom_linux")).toString();
//		binaryPathWindows = FileSystem.getLib(Paths.get("lib/countAntom_windows")).toString();
//		binaryPathMac = FileSystem.getLib(Paths.get("lib/countAntom_mac")).toString();
		binaryPathWindows = "";
		binaryPathMac = "";
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.analysis.cnf.solver.AExecutableSolver#parseResult(java.lang.String)
	 */
	@Override
	protected Object parseResult(String stdout) {
		final Pattern pattern = Pattern.compile("model count.*\\d*");
		final Matcher matcher = pattern.matcher(stdout);
		String result = "";
		if (matcher.find()) {
			result = matcher.group();
		} else {
			return 0;
		}
		final String[] split = result.split(" ");
		return new BigInteger(split[split.length - 1]);
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.analysis.cnf.solver.AExecutableSolver#execute()
	 */
	@Override
	public Object execute() {
		createTemporaryDimacs();
		final String stdout = runBinary(buildCommand());
		final BigInteger result = (BigInteger) parseResult(stdout);
		deleteTemporaryDimacs();
		return result;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.analysis.cnf.solver.AExecutableSolver#buildCommand()
	 */
	@Override
	protected String buildCommand() {
		// TODO: handle error at OS
		final String command =
			"/" + selectBinaryAccordingToOS() + " " + MEMORY_SIZE_FLAG + maxMemory + " " + NUMBER_OF_THREADS_FLAG + numberOfThreads + " " + DIMACS_TEMP_PATH;
		return command;
	}

	private String selectBinaryAccordingToOS() {
		final String osName = System.getProperty("os.name").toLowerCase();

		if (osName.indexOf("win") >= 0) {
			return binaryPathWindows;
		}
		if (osName.indexOf("mac") >= 0) {
			return binaryPathMac;
		}

		if ((osName.indexOf("nix") >= 0) || (osName.indexOf("nux") >= 0) || (osName.indexOf("aix") > 0)) {
			return binaryPathLinux;
		}
		return null;
	}

}
