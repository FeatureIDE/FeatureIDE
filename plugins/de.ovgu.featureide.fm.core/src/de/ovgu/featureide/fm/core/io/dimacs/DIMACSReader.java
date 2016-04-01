/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.LinkedList;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.remove.FeatureRemover;
import de.ovgu.featureide.fm.core.io.AbstractFeatureModelReader;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.job.ConsoleProgressMonitor;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.WorkMonitor;

/**
 * Parses feature models in the DIMACS CNF format.
 * 
 * @author Sebastian Krieter
 */
public class DIMACSReader extends AbstractFeatureModelReader {

	private String[] names = null;

	public DIMACSReader(final FeatureModel featureModel) {
		setFeatureModel(featureModel);
	}
	
	@Override
	protected void parseInputStream(InputStream inputStream) throws UnsupportedModelException {
		final LinkedList<String> sb = new LinkedList<>();
		try (BufferedReader r = new BufferedReader(new InputStreamReader(inputStream))) {
			String str = null;
			while ((str = r.readLine()) != null) {
				if (!str.isEmpty()) {
					sb.add(str);
					if (str.startsWith("p")) {
						final String[] startLine = str.split("\\s+");
						names = new String[Integer.parseInt(startLine[2]) + 1];
					}
				}
			}
		} catch (IOException e) {
			FMCorePlugin.getDefault().logError(e);
			return;
		}
		final Feature rootFeature = new Feature(featureModel);
		rootFeature.setAbstract(true);
		featureModel.addFeature(rootFeature);
		featureModel.setRoot(rootFeature);

		while (!sb.isEmpty()) {
			final String line = sb.removeFirst();
			if (line.startsWith("c")) {
				final String[] commentLine = line.split("\\s");
				final String id = commentLine[1].trim();
				final String name = commentLine[2].trim();
				names[Integer.parseInt(id)] = name;
			} else {
				break;
			}
		}

		final ArrayList<String> abstractNames = new ArrayList<>();
		for (int i = 1; i < names.length; i++) {
			final String name = getName(i);
			if (names[i] == null) {
				abstractNames.add(name);
			} else {
				final Feature feature = new Feature(featureModel, name);
				featureModel.addFeature(feature);
				rootFeature.addChild(feature);
			}
		}

		final ArrayList<Or> clauses = new ArrayList<>();
		final ArrayList<Literal> clauseParts = new ArrayList<>();
		while (!sb.isEmpty()) {
			final String[] clauseLine = sb.removeFirst().split("\\s");
			for (int i = 0; i < clauseLine.length - 1; i++) {
				final int varIndex = Integer.parseInt(clauseLine[i]);
				final String name = getName(Math.abs(varIndex));
				clauseParts.add(new Literal(name, varIndex > 0));
			}
			final Literal[] array = clauseParts.toArray(new Literal[0]);
			final Or propNode = new Or(array);
			clauses.add(propNode);
			clauseParts.clear();
		}
		Node cnf = new And(clauses.toArray(new Or[0]));
		final WorkMonitor workMonitor = new WorkMonitor();
		workMonitor.setMonitor(new ConsoleProgressMonitor());
		cnf = LongRunningWrapper.runMethod(new FeatureRemover(cnf, abstractNames, false), workMonitor);
		for (Node clause : cnf.getChildren()) {
			featureModel.addConstraint(new Constraint(featureModel, clause));
		}
		System.out.println("Done!");
	}

	private String getName(int varIndex) {
		String name = names[varIndex];
		return name != null ? name : "__Abstract__" + varIndex;
	}

}
