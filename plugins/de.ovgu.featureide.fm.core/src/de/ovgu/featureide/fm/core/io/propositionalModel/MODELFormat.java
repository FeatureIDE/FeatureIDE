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
package de.ovgu.featureide.fm.core.io.propositionalModel;

import java.io.IOException;
import java.text.ParseException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.prop4j.And;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.io.APersistentFormat;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;

/**
 * Reads and writes feature models in the MODEL CNF format.
 *
 * @author Sebastian Krieter
 * @author Timo G&uuml;nther
 */
public class MODELFormat extends APersistentFormat<IFeatureModel> implements IFeatureModelFormat {

	public static final String ID = PluginID.PLUGIN_ID + ".format.fm." + MODELFormat.class.getSimpleName();

	static final String ROOT_IDENTIFIER = "__Root__";

	static final String MODULE_FEATURE = "_MODULE";
	static final String MODULES_FEATURE = "MODULES";

	public static final String FEATURE_START = "#item";

	@Override
	public ProblemList read(IFeatureModel featureModel, CharSequence source) {
		final ProblemList problemList = new ProblemList();

		// Transform the input into a propositional node.
		final ModelReader r = new ModelReader();
		try {
			r.read(source.toString());
			addNodeToFeatureModel(featureModel, r.getFeatures(source.toString()), r.getClauses(source.toString()));
		} catch (final IllegalStateException | IOException e) {
			problemList.add(new Problem(e));
		} catch (final ParseException e) {
			problemList.add(new Problem(e, e.getErrorOffset()));
		}
		return problemList;
	}

	/**
	 * Adds the given propositional node to the given feature model. The current implementation is naive in that it does not attempt to interpret any constraint
	 * as {@link IFeatureStructure structure}.
	 *
	 * @param featureModel feature model to edit
	 * @param node propositional node to add
	 */
	private void addNodeToFeatureModel(IFeatureModel featureModel, ArrayList<String> features, Node node) {
		// Add a dummy feature as root.
		final IFeatureModelFactory factory = FMFactoryManager.getFactory(featureModel);

		final IFeature rootFeature = factory.createFeature(featureModel, ROOT_IDENTIFIER);
		FeatureUtils.setAbstract(rootFeature, true);
		FeatureUtils.addFeature(featureModel, rootFeature);
		FeatureUtils.setRoot(featureModel, rootFeature);

		// Add a features.
		for (final String featureName : features) {
			final IFeature feature = factory.createFeature(featureModel, featureName);
			FeatureUtils.addFeature(featureModel, feature);
			FeatureUtils.addChild(rootFeature, feature);
		}

		// Add a constraint for each conjunctive clause.
		final List<Node> clauses = node instanceof And ? Arrays.asList(node.getChildren()) : Collections.singletonList(node);
		for (final Node clause : clauses) {
			FeatureUtils.addConstraint(featureModel, factory.createConstraint(featureModel, clause));
		}
	}

	@Override
	public String write(IFeatureModel featureModel) {
		return new ModelWriter().write(NodeCreator.createNodes(featureModel));
	}

	@Override
	public String getSuffix() {
		return "model";
	}

	@Override
	public MODELFormat getInstance() {
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
	public String getName() {
		return "PropModel";
	}

}
