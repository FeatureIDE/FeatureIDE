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
package de.ovgu.featureide.fm.attributes.outlineentry;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.swt.graphics.Image;
import org.prop4j.solver.IOptimizationSolver;
import org.prop4j.solver.ISmtProblem;
import org.prop4j.solver.impl.SmtProblem;
import org.prop4j.solvers.impl.javasmt.sat.JavaSmtSatSolverFactory;
import org.prop4j.solvers.impl.javasmt.smt.JavaSmtSolver;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment.OptStatus;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.api.SolverException;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.DoubleFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.LongFeatureAttribute;
import de.ovgu.featureide.fm.attributes.computations.impl.EstimatedMinimumComputation;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.views.outline.IOutlineEntry;

public class AttributeMinimumEntry implements IOutlineEntry {

	IFeatureAttribute attribute;
	Configuration config;
	EstimatedMinimumComputation estimatedMinimum;
	Object result;
	private String labelSuffix;
	private boolean hasOptimaFound = false;

	private static final String EST = " (est)";
	private static final String LABEL = "Minimal sum of value: ";

	public AttributeMinimumEntry(Configuration config, IFeatureAttribute attribute) {
		this.config = config;
		this.attribute = attribute;
		estimatedMinimum = new EstimatedMinimumComputation(config, attribute);
		result = (Double) estimatedMinimum.getSelectionSum();
		labelSuffix = EST;

	}

	public Object getResult() {
		return result;
	}

	@Override
	public String getLabel() {
		if (result instanceof Long) {
			long resultLong = (Long) result;
			return LABEL + String.format("%d", resultLong) + labelSuffix;
		} else if (result instanceof Double) {
			double resultDouble = (Double) result;
			return LABEL + String.format("%.2f", resultDouble) + labelSuffix;
		}
		return LABEL + String.format("%.2f", result) + labelSuffix;
	}

	@Override
	public Image getLabelImage() {
		return null;
	}

	@Override
	public boolean hasChildren() {
		return false;
	}

	@Override
	public List<IOutlineEntry> getChildren() {
		return null;
	}

	@Override
	public boolean supportsType(Object element) {
		return attribute instanceof LongFeatureAttribute || attribute instanceof DoubleFeatureAttribute;
	}

	@Override
	public void setConfig(Configuration config) {
		this.config = config;

	}

	@Override
	public void handleDoubleClick() {
		if (hasOptimaFound) {
			return;
		}
		Object minimum = getOptimaMinimum();
		if (minimum instanceof Long) {
			result = (Double) minimum;
			hasOptimaFound = true;
		} else if (minimum instanceof Double) {
			result = (Double) minimum;
			hasOptimaFound = true;
		}
	}

	public Object getOptimaMinimum() {
		// Calculate optima
		// 1). Get Problem
		IFeatureModelManager fmManager = FeatureModelManager.getInstance(config.getFeatureModel());
		ISmtProblem problem =
			new SmtProblem(fmManager.getVariableFormula().getCNFNode(), FeatureUtils.getFeatureNamesList(fmManager.getVariableFormula().getFeatureModel()));

		// 2). Create optima solver with problem
		IOptimizationSolver solver = new JavaSmtSatSolverFactory().getOptimizationSolver(problem);
		if (solver instanceof JavaSmtSolver) {
			JavaSmtSolver z3Solver = (JavaSmtSolver) solver;
			FormulaManager fManager = z3Solver.context.getFormulaManager();
			BooleanFormulaManager bfm = fManager.getBooleanFormulaManager();
			RationalFormulaManager rfm = fManager.getRationalFormulaManager();

			try {
				for (SelectableFeature feature : config.getFeatures()) {
					if (feature.getSelection() == Selection.SELECTED) {
						z3Solver.prover.push(bfm.makeVariable(feature.getName()));
					} else if (feature.getSelection() == Selection.UNSELECTED) {
						z3Solver.prover.push(bfm.not(bfm.makeVariable(feature.getName())));
					}
				}
			} catch (InterruptedException e) {
				e.printStackTrace();
				return null;
			}

			List<NumeralFormula> formulas = new ArrayList<>();
			for (IFeature feature : fmManager.getVariableFormula().getFeatureModel().getFeatures()) {
				if (feature instanceof ExtendedFeature) {
					ExtendedFeature eFeature = (ExtendedFeature) feature;
					for (IFeatureAttribute att : eFeature.getAttributes()) {
						if (att.getName().equals(attribute.getName())) {
							if (att instanceof LongFeatureAttribute) {
								Long value = ((LongFeatureAttribute) att).getValue();
								if (value != null) {
									formulas.add(bfm.ifThenElse(bfm.makeVariable(att.getFeature().getName()), rfm.makeNumber(value), rfm.makeNumber(0L)));
								}
							} else if (att instanceof DoubleFeatureAttribute) {
								Double value = ((DoubleFeatureAttribute) att).getValue();
								if (value != null) {
									formulas.add(bfm.ifThenElse(bfm.makeVariable(att.getFeature().getName()), rfm.makeNumber(value), rfm.makeNumber(0D)));
								}
							}
						}
					}
				}
			}
			final int handle = z3Solver.prover.minimize(rfm.sum(formulas));

			OptStatus response;
			try {
				response = z3Solver.prover.check();
				assert response == OptStatus.OPT;
				labelSuffix = "";
				Object min = z3Solver.prover.lower(handle, Rational.ZERO).get().doubleValue();
				return min;
			} catch (InterruptedException e) {
				e.printStackTrace();
				return null;
			} catch (SolverException e) {
				e.printStackTrace();
				return null;
			}
		}
		return null;
	}

}
