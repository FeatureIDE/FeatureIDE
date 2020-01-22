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
package org.prop4j.solver.impl;

import org.eclipse.core.runtime.preferences.InstanceScope;
import org.osgi.service.prefs.Preferences;
import org.prop4j.solver.AbstractSolverFactory;
import org.prop4j.solver.impl.Ltms.LtmsSatSolverFactory;
import org.prop4j.solver.impl.sat4j.Sat4JSatSolverFactory;
import org.prop4j.solvers.impl.javasmt.sat.JavaSmtSatSolverFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;

import de.ovgu.featureide.fm.core.ExtensionManager;

/**
 * Responsible to load and save all information for a solver.
 *
 * @author Joshua Sprey
 */
public class SolverManager extends ExtensionManager<AbstractSolverFactory> {

	public final static String PREFERENCE_STORE_PATH = "de.ovgu.featureide.fm.ui.preferences.solver";
	public final static String FEATURE_MODEL_ANALYSIS_SOLVER = "featureModelAnalysisSolver";
	public final static String FEATURE_MODEL_DEFECT_SOLVER = "featureModelDefectSolver";
	public final static String OTHER_ANALYSES_SOLVER = "otherAnalysesSolver";

	private SolverManager() {}

	private static SolverManager instance = new SolverManager();

	public static Solvers solver = Solvers.SMTINTERPOL;

	public static SolverManager getInstance() {
		return instance;
	}

	public static AbstractSolverFactory getSelectedFeatureAttributeSolverFactory() {
		final Preferences preferences = InstanceScope.INSTANCE.getNode(PREFERENCE_STORE_PATH);
		final String solverID = preferences.get(FEATURE_MODEL_ANALYSIS_SOLVER, Sat4JSatSolverFactory.ID);
		try {
			return getInstance().getExtension(solverID).getNewFactory();
		} catch (final NoSuchExtensionException e) {
			return new Sat4JSatSolverFactory();
		}
	}

	public static void setSelectedFeatureAttributeSolverFactory(String solverFactoryID) {
		final Preferences preferences = InstanceScope.INSTANCE.getNode(PREFERENCE_STORE_PATH);
		if ((solverFactoryID == Sat4JSatSolverFactory.ID) || (solverFactoryID == JavaSmtSatSolverFactory.ID)) {
			preferences.put(FEATURE_MODEL_ANALYSIS_SOLVER, solverFactoryID);
		}
	}

	public static AbstractSolverFactory getSelectedFeatureModelDefectExplanatorSolverFactory() {
		final Preferences preferences = InstanceScope.INSTANCE.getNode(PREFERENCE_STORE_PATH);
		final String solverID = preferences.get(FEATURE_MODEL_DEFECT_SOLVER, LtmsSatSolverFactory.ID);
		try {
			final AbstractSolverFactory f = getInstance().getExtension(solverID).getNewFactory();
			if (f instanceof JavaSmtSatSolverFactory) {
				final JavaSmtSatSolverFactory factory = (JavaSmtSatSolverFactory) f;
				factory.solver = solver;
			}
			return f;
		} catch (final NoSuchExtensionException e) {
			return new LtmsSatSolverFactory();
		}
	}

	public static void setSelectedFeatureModelDefectExplanatorSolverFactory(String solverFactoryID) {
		final Preferences preferences = InstanceScope.INSTANCE.getNode(PREFERENCE_STORE_PATH);
		if ((solverFactoryID == Sat4JSatSolverFactory.ID) || (solverFactoryID == JavaSmtSatSolverFactory.ID)) {
			preferences.put(FEATURE_MODEL_DEFECT_SOLVER, solverFactoryID);
		}
	}

	public static AbstractSolverFactory getSelectedOtherAnalysesSolverFactory() {
		final Preferences preferences = InstanceScope.INSTANCE.getNode(PREFERENCE_STORE_PATH);
		final String solverID = preferences.get(OTHER_ANALYSES_SOLVER, Sat4JSatSolverFactory.ID);
		try {
			final AbstractSolverFactory f = getInstance().getExtension(solverID).getNewFactory();
			if (f instanceof JavaSmtSatSolverFactory) {
				final JavaSmtSatSolverFactory factory = (JavaSmtSatSolverFactory) f;
				factory.solver = solver;
			}
			return f;
		} catch (final NoSuchExtensionException e) {
			return new Sat4JSatSolverFactory();
		}
	}
}
