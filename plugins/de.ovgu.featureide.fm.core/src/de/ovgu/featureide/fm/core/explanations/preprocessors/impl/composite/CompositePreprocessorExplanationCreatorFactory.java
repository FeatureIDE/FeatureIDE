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
package de.ovgu.featureide.fm.core.explanations.preprocessors.impl.composite;

import java.util.Arrays;

import org.prop4j.solver.impl.Ltms.LtmsSatSolverFactory;
import org.prop4j.solvers.impl.javasmt.sat.JavaSmtSatSolverFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;

import de.ovgu.featureide.fm.core.explanations.preprocessors.InvariantPresenceConditionExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.preprocessors.PreprocessorExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.preprocessors.PreprocessorExplanationCreatorFactory;
import de.ovgu.featureide.fm.core.explanations.preprocessors.impl.mus.MusPreprocessorExplanationCreatorFactory;

/**
 * Provides instances of {@link PreprocessorExplanationCreator} using composition.
 *
 * @author Timo G&uuml;nther
 */
public class CompositePreprocessorExplanationCreatorFactory extends PreprocessorExplanationCreatorFactory {

	/** Factory for LTMS. */
	private final PreprocessorExplanationCreatorFactory ltms = new MusPreprocessorExplanationCreatorFactory(new LtmsSatSolverFactory());
	/** Factory for Sat4J MUS. */
	private final PreprocessorExplanationCreatorFactory musSat4j = new MusPreprocessorExplanationCreatorFactory();
	/** Factory for JavaSMT MUS. */
	private final PreprocessorExplanationCreatorFactory musJavaSMT =
		new MusPreprocessorExplanationCreatorFactory(new JavaSmtSatSolverFactory(Solvers.SMTINTERPOL));

	@Override
	public InvariantPresenceConditionExplanationCreator getInvariantPresenceConditionExplanationCreator() {
		return new CompositeInvariantPresenceConditionExplanationCreator(Arrays.asList(musJavaSMT.getInvariantPresenceConditionExplanationCreator()));
	}
}
