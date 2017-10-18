/*******************************************************************************
 * Copyright (c) 2013 University of Bergamo - Italy
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *   Paolo Vavassori - initial API and implementation
 *   Angelo Gargantini - utils and architecture
 ******************************************************************************/
package de.ovgu.featureide.fm.core.io.sxfm;

import javax.naming.OperationNotSupportedException;

import splar.core.fm.XMLFeatureModel;
import splar.core.heuristics.FTPreOrderSortedECTraversalHeuristic;
import splar.core.heuristics.VariableOrderingHeuristic;
import splar.core.heuristics.VariableOrderingHeuristicsManager;
import splar.plugins.reasoners.bdd.javabdd.FMReasoningWithBDD;
import splar.plugins.reasoners.bdd.javabdd.ReasoningWithBDD;

/**
 * @author garganti
 *
 */
public class Experiment_SPLOTmodels {

	protected splar.core.fm.FeatureModel getSplotModel(String featureModelPath) throws Exception {
		// Create feature model object from an XML file (SXFM format - see
		// www.splot-research.org for details)
		// If an identifier is not provided for a feature use the feature name
		// as id
		final splar.core.fm.FeatureModel featureModel = new XMLFeatureModel(featureModelPath, XMLFeatureModel.USE_VARIABLE_NAME_AS_ID);
		// load feature model from
		featureModel.loadModel();

		return featureModel;
	}

	/**
	 *
	 * @param featureModel
	 * @return number of valid configurations (using BDD)
	 * @throws Exception
	 * @throws OperationNotSupportedException
	 */
	protected long getNumberOfValidProducts(splar.core.fm.FeatureModel featureModel) throws Exception, OperationNotSupportedException {
		// create BDD variable order heuristic
		new FTPreOrderSortedECTraversalHeuristic("Pre-CL-MinSpan", featureModel, FTPreOrderSortedECTraversalHeuristic.FORCE_SORT);
		final VariableOrderingHeuristic heuristic = VariableOrderingHeuristicsManager.createHeuristicsManager().getHeuristic("Pre-CL-MinSpan");

		// Creates the BDD reasoner
		final ReasoningWithBDD reasoner = new FMReasoningWithBDD(featureModel, heuristic, 50000, 50000, 60000, "pre-order");

		// Initialize the reasoner (BDD is created at this moment)
		reasoner.init();
		// Use the reasoner
		// System.out.println("BDD has " + reasoner.getBDD().nodeCount()
		// + " nodes and was built in " + reasoner.getBDDBuildingTime()
		// + " ms " );

		// Check if feature model is consistent, i.e., has at least one valid
		// configuration
		assert (reasoner.isConsistent());
		// System.out.println("Feature model is "
		// + (reasoner.isConsistent() ? "" : " NOT ") + "consistent!");

		// Count feature model solutions
		// System.out.println("Feature model has "
//				+ reasoner.countValidConfigurations()
		// + " possible configurations");

		// Important:
		// - My research focused on heuristics to reduce the size of BDDs as
		// much as possible
		// (e.g. I proposed the "Pre-CL-MinSpan" heuristic above)
		// Therefore, there are plenty of opportunities for improving the
		// performance of many BDD reasoning operations provided
		// I actually know the algorithms but need time to code them
		// For now, use the BDD to check consistency of models and to count
		// valid configurations
		return (long) reasoner.countValidConfigurations();
	}

}
