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
package de.ovgu.featureide.fm.core.io.dimacs;

import java.text.ParseException;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.Node;
import org.prop4j.transform.DimacsReader;
import org.prop4j.transform.DimacsWriter;

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;

/**
 * Reads and writes feature models in the DIMACS CNF format.
 *
 * @author Sebastian Krieter
 * @author Timo G&uuml;nther
 */
public class DIMACSFormat implements IFeatureModelFormat {

	public static final String ID = PluginID.PLUGIN_ID + ".format.fm." + DIMACSFormat.class.getSimpleName();

	@Override
	public ProblemList read(IFeatureModel featureModel, CharSequence source) {
		final ProblemList problemList = new ProblemList();

		// Transform the input into a propositional node.
		final DimacsReader r = new DimacsReader(source.toString());
		r.setReadingVariableDirectory(true);
		final Node read;
		try {
			read = r.read();
		} catch (final ParseException e) {
			problemList.add(new Problem(e));
			return problemList;
		}

		// Add the propositional node to the feature model.
		addNodeToFeatureModel(featureModel, read);

		return problemList;
	}

	/**
	 * Adds the given propositional node to the given feature model. The current implementation is naive in that it does not attempt to interpret any constraint
	 * as {@link IFeatureStructure structure}.
	 *
	 * @param featureModel feature model to edit
	 * @param node propositional node to add
	 */
	private void addNodeToFeatureModel(IFeatureModel featureModel, Node node) {
		// Add a dummy feature as root.
		final IFeatureModelFactory factory = FMFactoryManager.getFactory(featureModel);
		final IFeature rootFeature = factory.createFeature(featureModel, "__Root__");
		rootFeature.getStructure().setAbstract(true);
		featureModel.addFeature(rootFeature);
		featureModel.getStructure().setRoot(rootFeature.getStructure());

		// Add a feature for each variable.
		final Set<String> variables = new LinkedHashSet<>(node.getContainedFeatures());
		for (final String variable : variables) {
			final IFeature feature = factory.createFeature(featureModel, variable);
			featureModel.addFeature(feature);
			rootFeature.getStructure().addChild(feature.getStructure());
		}

		// Add a constraint for each conjunctive clause.
		final List<Node> clauses = node instanceof And ? Arrays.asList(node.getChildren()) : Collections.singletonList(node);
		for (final Node clause : clauses) {
			final IConstraint constraint = factory.createConstraint(featureModel, clause);
			featureModel.addConstraint(constraint);
		}
	}

	@Override
	public String write(IFeatureModel featureModel) {
		final Node in = AdvancedNodeCreator.createRegularCNF(featureModel);
		final DimacsWriter w = new DimacsWriter(in);
		w.setWritingVariableDirectory(true);
		return w.write();
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
