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
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
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
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;

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
		final ArrayDeque<String> lines = new ArrayDeque<>();

		String[] names = null;
		int lineNumber = 1;
		try (BufferedReader r = new BufferedReader(new StringReader(source.toString()))) {
			String str = null;
			while ((str = r.readLine()) != null) {
				if (!str.isEmpty()) {
					str = str.trim();
					if (str.startsWith("p")) {
						final String[] startLine = str.split("\\s+");
						names = new String[Integer.parseInt(startLine[2]) + 1];
					} else {
						lines.add(str);
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

		while (!lines.isEmpty()) {
			final String line = lines.peek();
			if (line.startsWith("c")) {
				lines.poll();
				final String[] commentLine = line.split("\\s+");
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

		final ArrayList<String> abstractNames = new ArrayList<>();
		for (int i = 1; i < names.length; i++) {
			String name = names[i];
			if (name == null) {
				name = "__Abstract__" + i;
				abstractNames.add(name);
			}
			final IFeature feature = factory.createFeature(featureModel, name);
			featureModel.addFeature(feature);
			rootFeature.getStructure().addChild(feature.getStructure());
		}

		final ArrayList<Or> clauses = new ArrayList<>();
		while (!lines.isEmpty()) {
			final String[] clauseLine = lines.poll().split("\\s+");
			final Literal[] array = new Literal[clauseLine.length - 1];
			for (int i = 0; i < clauseLine.length - 1; i++) {
				final int varIndex = Integer.parseInt(clauseLine[i]);
				array[i] = new Literal(names[Math.abs(varIndex)], varIndex > 0);
			}
			final Or propNode = new Or(array);
			clauses.add(propNode);
		}
		Node cnf = new And(clauses.toArray(new Or[0]));

		//		final FeatureRemover remover = new FeatureRemover(cnf, abstractNames, false);
		//		cnf = remover.createNewClauseList(LongRunningWrapper.runMethod(remover, new ConsoleMonitor()));

		for (Node clause : cnf.getChildren()) {
			featureModel.addConstraint(factory.createConstraint(featureModel, clause));
		}
		return problemList;
	}

	@Override
	public String write(IFeatureModel featureModel) {
		final Node nodes = AdvancedNodeCreator.createCNF(featureModel);

		final StringBuilder stringBuilder = new StringBuilder();
		Map<String, Integer> featureMap = new HashMap<>();
		int i = 1;
		for (CharSequence name : FeatureUtils.extractFeatureNames(featureModel.getFeatures())) {
			featureMap.put(name.toString(), i);
			stringBuilder.append("c ");
			stringBuilder.append(i);
			stringBuilder.append(' ');
			stringBuilder.append(name.toString());
			stringBuilder.append(System.lineSeparator());
			i++;
		}

		int clauseCount = 0;
		final StringBuilder clauseStringBuilder = new StringBuilder();
		CHILDREN: for (Node and : nodes.getChildren()) {
			if (and instanceof Literal) {
				if (and.toString().equals("True") || and.toString().equals("-False")) {
					continue;
				}
				if (((Literal) and).positive) {
					clauseStringBuilder.append(featureMap.get(and.toString()));
				} else {
					clauseStringBuilder.append('-');
					clauseStringBuilder.append(featureMap.get(((Literal) and).var.toString()));
				}
				clauseStringBuilder.append(' ');
			} else {
				for (Node literal : and.getChildren()) {
					if (literal.toString().equals("True") || literal.toString().equals("-False")) {
						continue CHILDREN;
					}
				}

				for (Node literal : and.getChildren()) {
					if (((Literal) literal).positive) {
						clauseStringBuilder.append(featureMap.get(literal.toString()));
					} else {
						clauseStringBuilder.append('-');
						clauseStringBuilder.append(featureMap.get(((Literal) literal).var.toString()));
					}
					clauseStringBuilder.append(' ');
				}
			}
			clauseStringBuilder.append('0');
			clauseStringBuilder.append(System.lineSeparator());
			clauseCount++;
		}

		stringBuilder.append("p cnf ");
		stringBuilder.append(featureModel.getNumberOfFeatures());
		stringBuilder.append(' ');
		stringBuilder.append(clauseCount);
		stringBuilder.append(System.lineSeparator());
		stringBuilder.append(clauseStringBuilder);

		return stringBuilder.toString();
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

	@Override
	public boolean supportsContent(CharSequence content) {
		return supportsRead();
	}

}
