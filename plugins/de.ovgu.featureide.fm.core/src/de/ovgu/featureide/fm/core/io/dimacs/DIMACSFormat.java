/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.io.dimacs;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.remove.FeatureRemover;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.ConsoleMonitor;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Reads / Writes feature models in the DIMACS CNF format.
 * 
 * @author Sebastian Krieter
 */
public class DIMACSFormat implements IFeatureModelFormat {
	
	public static final String ID = PluginID.PLUGIN_ID + ".format.fm." + DIMACSFormat.class.getSimpleName();

	@Override
	public ProblemList read(IFeatureModel featureModel, CharSequence source) {
		final ProblemList problemList = new ProblemList();
		final LinkedList<String> sb = new LinkedList<>();

		String[] names = null;
		int lineNumber = 0;
		try (BufferedReader r = new BufferedReader(new StringReader(source.toString()))) {
			String str = null;
			while ((str = r.readLine()) != null) {
				if (!str.isEmpty()) {
					sb.add(str);
					if (str.startsWith("p")) {
						final String[] startLine = str.split("\\s+");
						names = new String[Integer.parseInt(startLine[2]) + 1];
					}
				}
				lineNumber++;
			}
		} catch (IOException e) {
			problemList.add(new Problem(e, lineNumber));
		}
		final IFeatureModelFactory factory = FMFactoryManager.getFactory(featureModel);
		final IFeature rootFeature = factory.createFeature(featureModel, "__Root__"); 
				
		rootFeature.getStructure().setAbstract(true);
		featureModel.addFeature(rootFeature);
		featureModel.getStructure().setRoot(rootFeature.getStructure());

		while (!sb.isEmpty()) {
			final String line = sb.removeFirst();
			if (line.startsWith("c")) {
				final String[] commentLine = line.split("\\s");
				final String id = commentLine[1].trim();
				final String name = commentLine[2].trim();
				try {
					names[Integer.parseInt(id)] = name;
				} catch (NumberFormatException e) {
				}
			} else {
				break;
			}
		}

		final HashSet<String> abstractNames = new HashSet<>();
		for (int i = 1; i < names.length; i++) {
			final String name = names[i];
			if (name != null) {
				final IFeature feature = factory.createFeature(featureModel, name); 
				featureModel.addFeature(feature);
				rootFeature.getStructure().addChild(feature.getStructure());
			}
		}

		final ArrayList<Or> clauses = new ArrayList<>();
		final ArrayList<Literal> clauseParts = new ArrayList<>();
		while (!sb.isEmpty()) {
			final String[] clauseLine = sb.removeFirst().split("\\s");
			for (int i = 0; i < clauseLine.length - 1; i++) {
				final int varIndex = Integer.parseInt(clauseLine[i]);
				String name = names[Math.abs(varIndex)];
				if (name == null) {
					name = "__Abstract__" + Math.abs(varIndex);
					abstractNames.add(name);
				}
				clauseParts.add(new Literal(name, varIndex > 0));
			}
			final Literal[] array = clauseParts.toArray(new Literal[0]);
			final Or propNode = new Or(array);
			clauses.add(propNode);
			clauseParts.clear();
		}
		Node cnf = new And(clauses.toArray(new Or[0]));
		final IMonitor workMonitor = new ConsoleMonitor();
		cnf = LongRunningWrapper.runMethod(new FeatureRemover(cnf, abstractNames, false), workMonitor);
		for (Node clause : cnf.getChildren()) {
			featureModel.addConstraint(factory.createConstraint(featureModel, clause));
		}
		return problemList;
	}

	@Override
	public String write(IFeatureModel featureModel) {
		final Node nodes = AdvancedNodeCreator.createCNF(featureModel);

		StringBuilder string = new StringBuilder();
		Map<String, Integer> featureMap = new HashMap<String, Integer>();
		int i = 1;
		for (CharSequence name : FeatureUtils.extractFeatureNames(featureModel.getFeatures())) {
			featureMap.put(name.toString(), i);
			string.append("c ");
			string.append(i);
			string.append(' ');
			string.append(name.toString());
			string.append(System.lineSeparator());
			i++;
		}
		string.append("p cnf ");
		string.append(featureModel.getNumberOfFeatures());
		string.append(' ');
		string.append(nodes.getChildren().length - 3);
		string.append("\r\n");

		for (Node and : nodes.getChildren()) {
			if (and instanceof Literal) {
				if (and.toString().equals("True") || and.toString().equals("-False")) {
					continue;
				}
				if (((Literal) and).positive) {
					string.append(featureMap.get(and.toString()));
				} else {
					string.append('-');
					string.append(featureMap.get(((Literal) and).var.toString()));
				}
				string.append(' ');
			} else {
				boolean skip = false;
				for (Node literal : and.getChildren()) {
					if (literal.toString().equals("True") || literal.toString().equals("-False")) {
						skip = true;
						break;
					}
				}
				if (skip) {
					continue;
				}

				for (Node literal : and.getChildren()) {
					if (((Literal) literal).positive) {
						string.append(featureMap.get(literal.toString()));
					} else {
						string.append('-');
						string.append(featureMap.get(((Literal) literal).var.toString()));
					}
					string.append(' ');
				}
			}
			string.append("0");
			string.append(System.lineSeparator());
		}

		return string.toString();
	}

	@Override
	public String getSuffix() {
		return "dimacs";
	}

	@Override
	public IPersistentFormat<IFeatureModel> getInstance() {
		return this;
	}

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public boolean supportsRead() {
		return true;
	}

	@Override
	public boolean supportsWrite() {
		return true;
	}

}
