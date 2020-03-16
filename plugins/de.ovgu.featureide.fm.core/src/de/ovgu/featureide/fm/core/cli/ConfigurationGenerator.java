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

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Random;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.SolutionList;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.AbstractAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.AllConfigurationGenerator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.IConfigurationGenerator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.PairWiseConfigurationGenerator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.RandomConfigurationGenerator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.SPLCAToolConfigurationGenerator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.TWiseConfigurationGenerator;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.csv.ConfigurationListFormat;
import de.ovgu.featureide.fm.core.io.dimacs.DIMACSFormatCNF;
import de.ovgu.featureide.fm.core.io.expression.ExpressionGroupFormat;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.ConsoleMonitor;

/**
 * Command line interface for sampling algorithms.
 *
 * @author Sebastian Krieter
 */
public class ConfigurationGenerator extends ACLIFunction {

	private String algorithm;
	private Path outputFile;
	private Path fmFile;
	private Path expressionFile;
	private Integer t;
	private Integer m;
	private Integer limit;
	private Long seed;

	@Override
	public String getId() {
		return "genconfig";
	}

	@Override
	public void run(List<String> args) {
		parseArguments(args);

		if (fmFile == null) {
			throw new IllegalArgumentException("No feature model specified!");
		}
		if (outputFile == null) {
			throw new IllegalArgumentException("No output file specified!");
		}
		if (algorithm == null) {
			throw new IllegalArgumentException("No algorithm specified!");
		}

		final CNF cnf = new CNF();
		ProblemList lastProblems = FileHandler.load(fmFile, cnf, new DIMACSFormatCNF());
		if (lastProblems.containsError()) {
			throw new IllegalArgumentException(lastProblems.getErrors().get(0).error);
		}

		final ArrayList<List<ClauseList>> expressionGroups;
		if (expressionFile != null) {
			expressionGroups = new ArrayList<>();
			lastProblems = FileHandler.load(expressionFile, expressionGroups, new ExpressionGroupFormat());
			if (lastProblems.containsError()) {
				throw new IllegalArgumentException(lastProblems.getErrors().get(0).error);
			}
		} else {
			expressionGroups = null;
		}

		IConfigurationGenerator generator = null;
		switch (algorithm.toLowerCase()) {
		case "icpl": {
			if (t == null) {
				throw new IllegalArgumentException("Value of t must be specified for icpl (use -t <value>)");
			}
			if (limit == null) {
				limit = Integer.MAX_VALUE;
			}
			generator = new SPLCAToolConfigurationGenerator(cnf, "ICPL", t, limit);
			break;
		}
		case "chvatal": {
			if (t == null) {
				throw new IllegalArgumentException("Value of t must be specified for chvatal (use -t <value>)");
			}
			if (limit == null) {
				limit = Integer.MAX_VALUE;
			}
			generator = new SPLCAToolConfigurationGenerator(cnf, "Chvatal", t, limit);
			break;
		}
		case "incling": {
			if (limit == null) {
				limit = Integer.MAX_VALUE;
			}
			generator = new PairWiseConfigurationGenerator(cnf, limit);
			if (seed == null) {
				((AbstractAnalysis<?>) generator).setRandom(new Random(seed));
			}
			break;
		}
		case "yasa": {
			if (t == null) {
				throw new IllegalArgumentException("Value of t must be specified for yasa (use -t <value>)");
			}
			if (limit == null) {
				limit = Integer.MAX_VALUE;
			}
			if (expressionGroups == null) {
				generator = new TWiseConfigurationGenerator(cnf, t, limit);
			} else {
				generator = new TWiseConfigurationGenerator(cnf, expressionGroups, t, limit);
			}
			if (m != null) {
				((TWiseConfigurationGenerator) generator).setIterations(m);
			}
			if (seed == null) {
				((AbstractAnalysis<?>) generator).setRandom(new Random(seed));
			}
			break;
		}
		case "random": {
			if (limit == null) {
				limit = Integer.MAX_VALUE;
			}
			generator = new RandomConfigurationGenerator(cnf, limit);
			((RandomConfigurationGenerator) generator).setAllowDuplicates(true);
			if (seed == null) {
				((AbstractAnalysis<?>) generator).setRandom(new Random(seed));
			}
			break;
		}
		case "all": {
			if (limit == null) {
				limit = Integer.MAX_VALUE;
			}
			generator = new AllConfigurationGenerator(cnf, limit);
			if (seed == null) {
				((AbstractAnalysis<?>) generator).setRandom(new Random(seed));
			}
			break;
		}
		default:
			throw new IllegalArgumentException("No algorithm specified!");
		}
		final List<LiteralSet> result = LongRunningWrapper.runMethod(generator, new ConsoleMonitor<>());
		FileHandler.save(outputFile, new SolutionList(cnf.getVariables(), result), new ConfigurationListFormat());
	}

	private void resetArguments() {
		algorithm = null;
		outputFile = null;
		fmFile = null;
		expressionFile = null;
		t = null;
		m = null;
		limit = null;
		seed = null;
	}

	private void parseArguments(List<String> args) {
		resetArguments();
		for (final Iterator<String> iterator = args.iterator(); iterator.hasNext();) {
			final String arg = iterator.next();
			if (arg.startsWith("-")) {
				switch (arg.substring(1)) {
				case "a": {
					algorithm = getArgValue(iterator, arg);
					break;
				}
				case "o": {
					outputFile = Paths.get(getArgValue(iterator, arg));
					break;
				}
				case "fm": {
					fmFile = Paths.get(getArgValue(iterator, arg));
					break;
				}
				case "t": {
					t = Integer.parseInt(getArgValue(iterator, arg));
					break;
				}
				case "m": {
					m = Integer.parseInt(getArgValue(iterator, arg));
					break;
				}
				case "l": {
					limit = Integer.parseInt(getArgValue(iterator, arg));
					break;
				}
				case "e": {
					expressionFile = Paths.get(getArgValue(iterator, arg));
					break;
				}
				case "s": {
					seed = Long.parseLong(getArgValue(iterator, arg));
					break;
				}
				default: {
					throw new IllegalArgumentException(arg);
				}
				}
			} else {
				throw new IllegalArgumentException(arg);
			}
		}
	}

	private String getArgValue(final Iterator<String> iterator, final String arg) {
		if (iterator.hasNext()) {
			return iterator.next();
		} else {
			throw new IllegalArgumentException("No value specified for " + arg);
		}
	}

	@Override
	public String getHelp() {
		final StringBuilder helpBuilder = new StringBuilder();
		helpBuilder.append("Help for command genconfig:\n");
		helpBuilder.append("\tGeneral Parameters:\n");
		helpBuilder.append("\t\t-fm <Path>   Specify path to feature model file.\n");
		helpBuilder.append("\t\t-o <Path>    Specify path to output file.\n");
		helpBuilder.append("\t\t-a <Name>    Specify algorithm by name. One of:\n");
		helpBuilder.append("\t\t                 icpl\n");
		helpBuilder.append("\t\t                 chvatal\n");
		helpBuilder.append("\t\t                 incling\n");
		helpBuilder.append("\t\t                 yasa\n");
		helpBuilder.append("\t\t                 random\n");
		helpBuilder.append("\t\t                 all\n");
		helpBuilder.append("\n");
		helpBuilder.append("\tAlgorithm Specific Parameters:\n");
		helpBuilder.append("\t\ticpl:\n");
		helpBuilder.append("\t\t\t-t <Value>    Specify value for t\n");
		helpBuilder.append("\t\t\t-l <Value>    Specify maximum number of configurations.\n");
		helpBuilder.append("\t\tchvatal:\n");
		helpBuilder.append("\t\t\t-t <Value>    Specify value for t\n");
		helpBuilder.append("\t\t\t-l <Value>    Specify maximum number of configurations.\n");
		helpBuilder.append("\t\tincling:\n");
		helpBuilder.append("\t\t\t-l <Value>    Specify maximum number of configurations.\n");
		helpBuilder.append("\t\t\t-s <Value>    Specify random seed.\n");
		helpBuilder.append("\t\tyasa:\n");
		helpBuilder.append("\t\t\t-t <Value>    Specify value for t\n");
		helpBuilder.append("\t\t\t-m <Value>    Specify value for m\n");
		helpBuilder.append("\t\t\t-l <Value>    Specify maximum number of configurations.\n");
		helpBuilder.append("\t\t\t-s <Value>    Specify random seed.\n");
		helpBuilder.append("\t\t\t-e <Path>     Specify path to expression file\n");
		helpBuilder.append("\t\trandom:\n");
		helpBuilder.append("\t\t\t-l <Value>    Specify maximum number of configurations.\n");
		helpBuilder.append("\t\t\t-s <Value>    Specify random seed.\n");
		helpBuilder.append("\t\tall:\n");
		helpBuilder.append("\t\t\t-l <Value>    Specify maximum number of configurations.\n");
		helpBuilder.append("\t\t\t-s <Value>    Specify random seed.\n");
		return helpBuilder.toString();
	}

}
