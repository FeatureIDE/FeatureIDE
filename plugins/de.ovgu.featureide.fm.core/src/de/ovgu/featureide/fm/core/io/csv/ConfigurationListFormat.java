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
package de.ovgu.featureide.fm.core.io.csv;

import java.util.Arrays;
import java.util.Scanner;
import java.util.regex.Pattern;

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet.Order;
import de.ovgu.featureide.fm.core.analysis.cnf.SolutionList;
import de.ovgu.featureide.fm.core.analysis.cnf.Variables;
import de.ovgu.featureide.fm.core.io.APersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * Reads / Writes a list of configuration.
 *
 * @author Sebastian Krieter
 */
public class ConfigurationListFormat extends APersistentFormat<SolutionList> {

	public static final String ID = PluginID.PLUGIN_ID + ".format.fm." + ConfigurationListFormat.class.getSimpleName();

	@Override
	public String write(SolutionList configurationList) {
		final StringBuilder csv = new StringBuilder();
		csv.append("Configuration");
		final String[] names = configurationList.getVariables().getNames();
		for (int i = 1; i < names.length; i++) {
			csv.append(';');
			csv.append(names[i]);
		}
		csv.append('\n');
		int configurationIndex = 0;
		for (final LiteralSet configuration : configurationList.getSolutions()) {
			csv.append(configurationIndex++);
			final int[] literals = configuration.getLiterals();
			for (int i = 0; i < literals.length; i++) {
				csv.append(';');
				csv.append(literals[i] < 0 ? 0 : 1);
			}
			csv.append('\n');
		}
		return csv.toString();
	}

	@Override
	public ProblemList read(SolutionList configurationList, CharSequence source) {
		final ProblemList problems = new ProblemList();
		int lineNumber = 0;
		try (final Scanner scanner = new Scanner(source.toString())) {
			scanner.useDelimiter(Pattern.compile("\\n+\\Z|\\n+|\\Z"));
			{
				final String line = scanner.next();
				if (line.trim().isEmpty()) {
					problems.add(new Problem(new UnsupportedModelException("Empty file!", lineNumber)));
					return problems;
				}
				final String[] names = line.split(";");
				configurationList.setVariables(new Variables(Arrays.asList(names).subList(1, names.length)));
			}

			while (scanner.hasNext()) {
				final String line = scanner.next();
				lineNumber++;
				final String[] split = line.split(";");
				if ((split.length - 1) != configurationList.getVariables().size()) {
					problems.add(new Problem(new UnsupportedModelException("Number of selections does not match number of features!", lineNumber)));
					return problems;
				}
				final int[] literals = new int[configurationList.getVariables().size()];
				for (int i = 1; i < split.length; i++) {
					literals[i - 1] = split[i].equals("0") ? -i : i;
				}
				configurationList.addSolution(new LiteralSet(literals, Order.INDEX, false));
			}
		} catch (final Exception e) {
			problems.add(new Problem(new UnsupportedModelException(e.getMessage(), lineNumber)));
		}
		return problems;
	}

	@Override
	public String getSuffix() {
		return "csv";
	}

	@Override
	public ConfigurationListFormat getInstance() {
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
	public boolean supportsRead() {
		return true;
	}

	@Override
	public String getName() {
		return "ConfigurationList";
	}

}
