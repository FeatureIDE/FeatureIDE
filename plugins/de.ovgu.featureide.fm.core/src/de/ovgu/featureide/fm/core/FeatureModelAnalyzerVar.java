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
package de.ovgu.featureide.fm.core;

import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.annotation.CheckForNull;

import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.analysis.ConstraintProperties;
import de.ovgu.featureide.fm.core.analysis.ConstraintProperties.ConstraintDeadStatus;
import de.ovgu.featureide.fm.core.analysis.ConstraintProperties.ConstraintFalseOptionalStatus;
import de.ovgu.featureide.fm.core.analysis.ConstraintProperties.ConstraintFalseSatisfiabilityStatus;
import de.ovgu.featureide.fm.core.analysis.ConstraintProperties.ConstraintRedundancyStatus;
import de.ovgu.featureide.fm.core.analysis.FeatureModelProperties;
import de.ovgu.featureide.fm.core.analysis.FeatureProperties;
import de.ovgu.featureide.fm.core.analysis.FeatureProperties.FeatureDeterminedStatus;
import de.ovgu.featureide.fm.core.analysis.FeatureProperties.FeatureParentStatus;
import de.ovgu.featureide.fm.core.analysis.FeatureProperties.FeatureSelectionStatus;
import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.IVariables;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.Nodes;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.AbstractAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.AnalysisResult;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.AtomicSetAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.CauseAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.CauseAnalysis.Anomalies;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.ContradictionAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.CoreDeadAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.HasSolutionAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.IndependentContradictionAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.IndependentRedundancyAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.IndeterminedAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.RedundancyAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.EmptyCNFCreator;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureTreeCNFCreator;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.ExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.fm.DeadFeatureExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.fm.FalseOptionalFeatureExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelExplanationCreatorFactory;
import de.ovgu.featureide.fm.core.explanations.fm.RedundantConstraintExplanationCreator;
import de.ovgu.featureide.fm.core.filter.FeatureSetFilter;
import de.ovgu.featureide.fm.core.filter.HiddenFeatureFilter;
import de.ovgu.featureide.fm.core.filter.MandatoryFeatureFilter;
import de.ovgu.featureide.fm.core.filter.OptionalFeatureFilter;
import de.ovgu.featureide.fm.core.filter.base.InverseFilter;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.functional.Functional.IFunction;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.NullMonitor;

/**
 * A collection of methods for working with {@link IFeatureModel} will replace
 * the corresponding methods in {@link IFeatureModel}
 * 
 * @author Soenke Holthusen
 * @author Florian Proksch
 * @author Stefan Krueger
 * @author Marcus Pinnecke (Feature Interface)
 */
public class FeatureModelAnalyzerVar {
	/**
	 * Remembers explanations for dead features.
	 */
	private final Map<IFeature, Explanation> deadFeatureExplanations = new HashMap<>();
	/**
	 * Remembers explanations for false-optional features.
	 */
	private final Map<IFeature, Explanation> falseOptionalFeatureExplanations = new HashMap<>();
	/**
	 * Remembers explanations for redundant constraints.
	 */
	private final Map<IConstraint, Explanation> redundantConstraintExplanations = new HashMap<>();
	/**
	 * Used for creating explanation creators.
	 */
	private final FeatureModelExplanationCreatorFactory explanationCreatorFactory = FeatureModelExplanationCreatorFactory.getDefault();
	/**
	 * Creates explanations for dead features.
	 * Stored for performance so the underlying CNF is not recreated for every explanation.
	 */
	private final DeadFeatureExplanationCreator deadFeatureExplanationCreator = explanationCreatorFactory.getDeadFeatureExplanationCreator();
	/**
	 * Creates explanations for false-optional features.
	 * Stored for performance so the underlying CNF is not recreated for every explanation.
	 */
	private final FalseOptionalFeatureExplanationCreator falseOptionalFeatureExplanationCreator = explanationCreatorFactory
			.getFalseOptionalFeatureExplanationCreator();
	/**
	 * Creates explanations for redundant constraints.
	 * Stored for performance so the underlying CNF is not recreated for every explanation.
	 */
	private final RedundantConstraintExplanationCreator redundantConstraintExplanationCreator = explanationCreatorFactory
			.getRedundantConstraintExplanationCreator();

	private static class AnalysisWrapper<R> {

		private Object syncObject = new Object();
		private IMonitor monitor = new NullMonitor();
		private boolean enabled = true;

		private AnalysisResult<R> analysisResult;

		public R getResult(AnalysisCreator<R, ? extends AbstractAnalysis<R>> analysis) {
			if (!enabled) {
				return null;
			}

			AnalysisResult<R> curAnalysisResult;
			IMonitor curMonitor;
			Object curSyncObject;
			synchronized (this) {
				curAnalysisResult = this.analysisResult;
				curMonitor = this.monitor;
				curSyncObject = this.syncObject;
			}

			synchronized (curSyncObject) {
				if (curAnalysisResult == null) {
					AbstractAnalysis<R> analysisInstance = analysis.createNewAnalysis();
					try {
						LongRunningWrapper.runMethod(analysisInstance, curMonitor);
						curAnalysisResult = analysisInstance.getResult();
					} catch (Exception e) {
						Logger.logError(e);
					}

					synchronized (this) {
						if (curSyncObject == this.syncObject) {
							this.analysisResult = curAnalysisResult;
							this.monitor = new NullMonitor();
						}
					}
				}
				return curAnalysisResult.getResult();
			}
		}

		public boolean isEnabled() {
			return enabled;
		}

		public void setEnabled(boolean enabled) {
			this.enabled = enabled;
		}

		public void reset() {
			synchronized (this) {
				analysisResult = null;
				monitor.cancel();
				monitor = new NullMonitor();
				syncObject = new Object();
			}
		}

	}

	public static class StringToFeature implements IFunction<String, IFeature> {
		private final IFeatureModel featureModel;

		public StringToFeature(IFeatureModel featureModel) {
			this.featureModel = featureModel;
		}

		@Override
		public IFeature invoke(String name) {
			return featureModel.getFeature(name);
		}
	};

	private class AnalysisCreator<R, A extends AbstractAnalysis<R>> {

		private final Class<A> analysis;

		public AnalysisCreator(Class<A> analysis) {
			this.analysis = analysis;
		}

		public CNF getCNF() {
			return formula.getCNF();
		}

		public A createNewAnalysis() {
			try {
				final CNF cnf = getCNF();
				final A newInstance = analysis.getConstructor(CNF.class).newInstance(cnf);
				configureAnalysis(cnf, newInstance);
				return newInstance;
			} catch (InstantiationException | IllegalAccessException | IllegalArgumentException | InvocationTargetException | NoSuchMethodException
					| SecurityException e) {
				throw new AssertionError();
			}
		}

		protected void configureAnalysis(CNF cnf, A analysis) {
		}

	}

	/**
	 * Defines whether features should be included into calculations.
	 * If features are not analyzed, then constraints a also NOT analyzed.
	 */
	private boolean calculateFeatures = true;
	/**
	 * Defines whether constraints should be included into calculations.
	 */
	private boolean calculateConstraints = true;

	/**
	 * Defines whether analysis should be performed automatically.
	 */
	private boolean runCalculationAutomatically = true;

	/**
	 * Remembers results for analyzed features.
	 */
	private final Map<IFeature, FeatureProperties> featurePropertiesMap;

	/**
	 * Remembers results for analyzed constraints.
	 */
	private final Map<IConstraint, ConstraintProperties> constraintPropertiesMap;
	/**
	 * Remembers results for analyzed constraints and features.
	 */
	private final Map<IFeatureModelElement, Object> elementPropertiesMap;

	/**
	 * Remembers results for analyzed feature model.
	 */
	private FeatureModelProperties featureModelProperties;

	private FeatureModelFormula formula;
	private IFeatureModel featureModel;
	private List<IConstraint> constraints;

	private int[] clauseGroupSize;
	private List<LiteralSet> constraintClauses;

	private final AnalysisWrapper<Boolean> validAnalysis = new AnalysisWrapper<>();
	private final AnalysisWrapper<List<LiteralSet>> atomicSetAnalysis = new AnalysisWrapper<>();
	private final AnalysisWrapper<LiteralSet> coreDeadAnalysis = new AnalysisWrapper<>();
	private final AnalysisWrapper<List<LiteralSet>> foAnalysis = new AnalysisWrapper<>();
	private final AnalysisWrapper<LiteralSet> determinedAnalysis = new AnalysisWrapper<>();
	private final AnalysisWrapper<List<LiteralSet>> constraintRedundancyAnalysis = new AnalysisWrapper<>();
	private final AnalysisWrapper<List<LiteralSet>> constraintTautologyAnalysis = new AnalysisWrapper<>();
	private final AnalysisWrapper<List<Anomalies>> constraintAnomaliesAnalysis = new AnalysisWrapper<>();
	private final AnalysisWrapper<List<LiteralSet>> constraintContradictionAnalysis = new AnalysisWrapper<>();
	private final AnalysisWrapper<List<LiteralSet>> constraintVoidAnalysis = new AnalysisWrapper<>();

	private final List<AnalysisWrapper<?>> list = Arrays.asList(validAnalysis, atomicSetAnalysis, coreDeadAnalysis, foAnalysis, determinedAnalysis,
			constraintContradictionAnalysis, constraintVoidAnalysis, constraintTautologyAnalysis, constraintRedundancyAnalysis, constraintAnomaliesAnalysis);

	public void reset(IFeatureModel featureModel) {
		for (AnalysisWrapper<?> analysisWrapper : list) {
			analysisWrapper.reset();
		}
		init(featureModel);
	}

	private void init(IFeatureModel featureModel) {
		constraints = featureModel.getConstraints();
		constraintClauses = new ArrayList<>();
		clauseGroupSize = getClauseGroups(constraints, constraintClauses);

		featurePropertiesMap.clear();
		constraintPropertiesMap.clear();

		for (IFeature feature : featureModel.getFeatures()) {
			final FeatureProperties featureProperties = new FeatureProperties(feature);
			featurePropertiesMap.put(feature, featureProperties);
			elementPropertiesMap.put(feature, featureProperties);
		}
		for (IConstraint constraint : featureModel.getConstraints()) {
			final ConstraintProperties constraintProperties = new ConstraintProperties(constraint);
			constraintPropertiesMap.put(constraint, constraintProperties);
			elementPropertiesMap.put(constraint, constraintProperties);
		}
		featureModelProperties = new FeatureModelProperties(featureModel, featurePropertiesMap.values(), constraintPropertiesMap.values());

		clearExplanations();
	}

	public FeatureModelAnalyzerVar(IFeatureModel featureModel) {
		this(new FeatureModelFormula(featureModel));
	}

	public FeatureModelAnalyzerVar(FeatureModelFormula formula) {
		this.formula = formula;
		this.featureModel = formula.getFeatureModel();

		featurePropertiesMap = new HashMap<>();
		constraintPropertiesMap = new HashMap<>();
		elementPropertiesMap = new HashMap<>();

		init(featureModel);
	}

	protected int[] getClauseGroups(List<IConstraint> constraints, List<LiteralSet> constraintClauses) {
		int[] clauseGroupSize = new int[constraints.size()];
		final IVariables variables = formula.getElement(new EmptyCNFCreator()).getVariables();
		int i = 0;
		for (IConstraint constraint : constraints) {
			final List<LiteralSet> clauses = Nodes.convert(variables, constraint.getNode());
			constraintClauses.addAll(clauses);
			clauseGroupSize[i++] = clauses.size();
		}
		return clauseGroupSize;
	}

	public boolean isValid() {
		final Boolean result = validAnalysis.getResult(new AnalysisCreator<>(HasSolutionAnalysis.class));
		return result == null ? false : result;
	}

	public List<IFeature> getCoreFeatures() {
		final LiteralSet result = coreDeadAnalysis.getResult(new AnalysisCreator<>(CoreDeadAnalysis.class));
		if (result == null) {
			return Collections.emptyList();
		}
		return Functional.mapToList(formula.getCNF().getVariables().convertToString(result, true, false, false), new StringToFeature(featureModel));
	}

	public List<IFeature> getDeadFeatures() {
		final LiteralSet result = coreDeadAnalysis.getResult(new AnalysisCreator<>(CoreDeadAnalysis.class));
		if (result == null) {
			return Collections.emptyList();
		}
		return Functional.mapToList(formula.getCNF().getVariables().convertToString(result, false, true, false), new StringToFeature(featureModel));
	}

	/**
	 * Returns the list of features that occur in all variants, where one of the
	 * given features is selected. If the given list of features is empty, this
	 * method will calculate the features that are present in all variants
	 * specified by the feature model.
	 * 
	 * @return a list of features that is common to all variants
	 */
	public List<IFeature> getCommonFeatures() {
		final LiteralSet result = coreDeadAnalysis.getResult(new AnalysisCreator<>(CoreDeadAnalysis.class));
		if (result == null) {
			return Collections.emptyList();
		}
		final Set<IFeature> uncommonFeatures = Functional
				.toSet(Functional.map(formula.getCNF().getVariables().convertToString(result, true, true, false), new StringToFeature(featureModel)));
		return Functional.mapToList(featureModel.getFeatures(), new InverseFilter<>(new FeatureSetFilter(uncommonFeatures)),
				new Functional.IdentityFunction<IFeature>());
	}

	public List<List<IFeature>> getAtomicSets() {
		final List<LiteralSet> result = atomicSetAnalysis.getResult(new AnalysisCreator<>(AtomicSetAnalysis.class));
		if (result == null) {
			return Collections.emptyList();
		}

		final CNF cnf = formula.getCNF();
		final ArrayList<List<IFeature>> resultList = new ArrayList<>();
		for (LiteralSet literalList : result) {
			final List<IFeature> setList = new ArrayList<>();
			resultList.add(Functional.mapToList(cnf.getVariables().convertToString(literalList, true, true, false), new StringToFeature(featureModel)));

			for (int literal : literalList.getLiterals()) {
				final IFeature feature = featureModel.getFeature(cnf.getVariables().getName(literal));
				if (feature != null) {
					setList.add(feature);
				}
			}

		}
		return resultList;
	}

	/**
	 * Calculations for indeterminate hidden features
	 * 
	 * @param changedAttributes
	 */
	public List<IFeature> getIndeterminedHiddenFeatures() {
		final AnalysisCreator<LiteralSet, IndeterminedAnalysis> analysisCreator = new AnalysisCreator<LiteralSet, IndeterminedAnalysis>(
				IndeterminedAnalysis.class) {
			@Override
			protected void configureAnalysis(CNF cnf, IndeterminedAnalysis analysis) {
				final LiteralSet convertToVariables = cnf.getVariables()
						.convertToVariables(Functional.mapToList(featureModel.getFeatures(), new HiddenFeatureFilter(), FeatureUtils.GET_FEATURE_NAME));
				analysis.setVariables(convertToVariables);
			}
		};
		final LiteralSet result = determinedAnalysis.getResult(analysisCreator);
		if (result == null) {
			return Collections.emptyList();
		}
		return Functional.mapToList(formula.getCNF().getVariables().convertToString(result, true, false, false), new StringToFeature(featureModel));
	}

	public List<IFeature> getFalseOptionalFeatures() {
		final List<IFeature> optionalFeatures = Functional.filterToList(featureModel.getFeatures(), new InverseFilter<>(new MandatoryFeatureFilter()));
		List<LiteralSet> result = getFalseOptionalFeatures(optionalFeatures);

		final List<IFeature> resultList = new ArrayList<>();
		int i = 0;
		for (IFeature iFeature : optionalFeatures) {
			if (result.get(i++) != null) {
				resultList.add(iFeature);
			}
		}

		return resultList;
	}

	protected List<LiteralSet> getFalseOptionalFeatures(final List<IFeature> optionalFeatures) {
		final AnalysisCreator<List<LiteralSet>, IndependentRedundancyAnalysis> analysisCreator = new AnalysisCreator<List<LiteralSet>, IndependentRedundancyAnalysis>(
				IndependentRedundancyAnalysis.class) {
			@Override
			protected void configureAnalysis(CNF cnf, IndependentRedundancyAnalysis analysis) {
				final List<LiteralSet> literalSetList = new ArrayList<>();
				final IVariables variables = cnf.getVariables();
				for (IFeature iFeature : optionalFeatures) {
					literalSetList.add(new LiteralSet(variables.getVariable(FeatureUtils.getParent(iFeature).getName(), false),
							variables.getVariable(iFeature.getName(), true)));
				}
				analysis.setClauseList(literalSetList);
			}
		};
		final List<LiteralSet> result = foAnalysis.getResult(analysisCreator);
		if (result == null) {
			return Collections.emptyList();
		}
		return result;
	}

	public List<IConstraint> getContradictoryConstraints() {
		final List<IConstraint> constraints = getVoidConstraints();
		final ArrayList<LiteralSet> constraintClauses = new ArrayList<>();
		final int[] clauseGroupSize = getClauseGroups(constraints, constraintClauses);

		final AnalysisCreator<List<LiteralSet>, IndependentContradictionAnalysis> analysisCreator = new AnalysisCreator<List<LiteralSet>, IndependentContradictionAnalysis>(
				IndependentContradictionAnalysis.class) {
			@Override
			public CNF getCNF() {
				return formula.getElement(new EmptyCNFCreator());
			}

			@Override
			protected void configureAnalysis(CNF cnf, IndependentContradictionAnalysis analysis) {
				analysis.setClauseList(constraintClauses);
				analysis.setClauseGroupSize(clauseGroupSize);
			}
		};

		final List<LiteralSet> result = constraintContradictionAnalysis.getResult(analysisCreator);
		if (result == null) {
			return Collections.emptyList();
		}

		final List<IConstraint> resultList = new ArrayList<>();
		for (int i = 0; i < clauseGroupSize.length; i++) {
			if (result.get(i) != null) {
				resultList.add(constraints.get(i));
			}
		}
		return resultList;
	}

	public List<IConstraint> getVoidConstraints() {
		final AnalysisCreator<List<LiteralSet>, ContradictionAnalysis> analysisCreator = new AnalysisCreator<List<LiteralSet>, ContradictionAnalysis>(
				ContradictionAnalysis.class) {
			@Override
			public CNF getCNF() {
				return formula.getElement(new FeatureTreeCNFCreator());
			}

			@Override
			protected void configureAnalysis(CNF cnf, ContradictionAnalysis analysis) {
				analysis.setClauseList(constraintClauses);
				analysis.setClauseGroupSize(clauseGroupSize);
			}
		};
		final List<LiteralSet> result = constraintVoidAnalysis.getResult(analysisCreator);
		if (result == null) {
			return Collections.emptyList();
		}

		final List<IConstraint> resultList = new ArrayList<>();
		for (int i = 0; i < clauseGroupSize.length; i++) {
			if (result.get(i) != null) {
				resultList.add(constraints.get(i));
			}
		}
		return resultList;
	}

	public List<IConstraint> getAnomalyConstraints() {
		final AnalysisCreator<List<Anomalies>, CauseAnalysis> analysisCreator = new AnalysisCreator<List<Anomalies>, CauseAnalysis>(CauseAnalysis.class) {
			@Override
			public CNF getCNF() {
				return formula.getElement(new FeatureTreeCNFCreator());
			}

			@Override
			protected void configureAnalysis(CNF cnf, CauseAnalysis analysis) {
				final Anomalies initialAnomalies = new Anomalies();
				initialAnomalies.setDeadVariables(coreDeadAnalysis.getResult(new AnalysisCreator<>(CoreDeadAnalysis.class)));
				initialAnomalies.setRedundantClauses(
						Functional.removeNull(getFalseOptionalFeatures(Functional.filterToList(featureModel.getFeatures(), new OptionalFeatureFilter()))));

				analysis.setAnomalies(initialAnomalies);
				analysis.setClauseList(constraintClauses);
				analysis.setClauseGroupSize(clauseGroupSize);
			}
		};

		final List<Anomalies> result = constraintAnomaliesAnalysis.getResult(analysisCreator);
		if (result == null) {
			return Collections.emptyList();
		}

		final CNF cnf = formula.getCNF();

		final List<IConstraint> resultList = new ArrayList<>();
		for (int i = 0; i < clauseGroupSize.length; i++) {
			final Anomalies anomalies = result.get(i);
			if (anomalies != null) {
				if (anomalies.getRedundantClauses() != null) {
					final ArrayList<IFeature> falseOptionalFeatures = new ArrayList<>();
					for (LiteralSet literalSet : anomalies.getRedundantClauses()) {
						if (literalSet != null) {
							falseOptionalFeatures.add(featureModel.getFeature(cnf.getVariables().getName(literalSet.getLiterals()[1])));
						}
					}
					final IConstraint constraint = constraints.get(i);
					getConstraintProperties(constraint).setFalseOptionalFeatures(falseOptionalFeatures);
					resultList.add(constraint);
				}
				if (anomalies.getDeadVariables() != null) {
					final IConstraint constraint = constraints.get(i);
					getConstraintProperties(constraint).setDeadFeatures(Functional.mapToList(
							cnf.getVariables().convertToString(anomalies.getDeadVariables(), false, true, false), new StringToFeature(featureModel)));
					resultList.add(constraint);
				}
			}
		}

		return resultList;
	}

	public List<IConstraint> getTautologyConstraints() {
		final List<IConstraint> constraints = getRedundantConstraints();
		final ArrayList<LiteralSet> constraintClauses = new ArrayList<>();
		final int[] clauseGroupSize = getClauseGroups(constraints, constraintClauses);

		final AnalysisCreator<List<LiteralSet>, IndependentRedundancyAnalysis> analysisCreator = new AnalysisCreator<List<LiteralSet>, IndependentRedundancyAnalysis>(
				IndependentRedundancyAnalysis.class) {
			@Override
			public CNF getCNF() {
				return formula.getElement(new EmptyCNFCreator());
			}

			@Override
			protected void configureAnalysis(CNF cnf, IndependentRedundancyAnalysis analysis) {
				analysis.setClauseList(constraintClauses);
				analysis.setClauseGroupSize(clauseGroupSize);
			}
		};

		final List<LiteralSet> result = constraintTautologyAnalysis.getResult(analysisCreator);
		if (result == null) {
			return Collections.emptyList();
		}

		final List<IConstraint> resultList = new ArrayList<>();
		for (int i = 0; i < clauseGroupSize.length; i++) {
			if (result.get(i) != null) {
				resultList.add(constraints.get(i));
			}
		}
		return resultList;
	}

	public List<IConstraint> getRedundantConstraints() {
		final AnalysisCreator<List<LiteralSet>, RedundancyAnalysis> analysisCreator = new AnalysisCreator<List<LiteralSet>, RedundancyAnalysis>(
				RedundancyAnalysis.class) {
			@Override
			public CNF getCNF() {
				return formula.getElement(new FeatureTreeCNFCreator());
			}

			@Override
			protected void configureAnalysis(CNF cnf, RedundancyAnalysis analysis) {
				analysis.setClauseList(constraintClauses);
				analysis.setClauseGroupSize(clauseGroupSize);
			}
		};
		final List<LiteralSet> result = constraintRedundancyAnalysis.getResult(analysisCreator);
		if (result == null) {
			return Collections.emptyList();
		}

		final List<IConstraint> resultList = new ArrayList<>();
		for (int i = 0; i < clauseGroupSize.length; i++) {
			if (result.get(i) != null) {
				resultList.add(constraints.get(i));
			}
		}
		return resultList;
	}

	public FeatureProperties getFeatureProperties(IFeature feature) {
		return featurePropertiesMap.get(feature);
	}

	public ConstraintProperties getConstraintProperties(IConstraint constraint) {
		return constraintPropertiesMap.get(constraint);
	}

	public FeatureModelProperties getFeatureModelProperties() {
		return featureModelProperties;
	}

	/**
	 * @param monitor
	 * @return
	 * @return Hashmap: key entry is Feature/Constraint, value usually
	 *         indicating the kind of attribute
	 */
	/*
	 * check all changes of this method and called methods with the related tests and
	 * benchmarks, see fm.core-test plug-in
	 * think about performance (no unnecessary or redundant calculations)
	 * 
	 * Hashing might be fast for locating features, but creating a HashSet is costly 
	 * So LinkedLists are much faster because the number of feature in the set is usually small (e.g. dead features)
	 */
	public Map<IFeatureModelElement, Object> analyzeFeatureModel(IMonitor monitor) {
		// TODO !!! use monitor
		if (monitor == null) {
			monitor = new NullMonitor();
		}

		updateFeatures(monitor);

		updateConstraints(monitor);

		return elementPropertiesMap;
	}

	public void updateConstraints() {
		updateConstraints(null);
	}

	public void updateConstraints(IMonitor monitor) {
		if (calculateConstraints) {
			if (monitor == null) {
				monitor = new NullMonitor();
			}
			// set default values for constraint properties
			for (IConstraint constraint : featureModel.getConstraints()) {
				if (constraintRedundancyAnalysis.isEnabled()) {
					constraintPropertiesMap.get(constraint).setConstraintRedundancyStatus(ConstraintRedundancyStatus.NORMAL);
				}
				if (constraintVoidAnalysis.isEnabled()) {
					constraintPropertiesMap.get(constraint).setConstraintSatisfiabilityStatus(ConstraintFalseSatisfiabilityStatus.SATISFIABLE);
				}
				if (constraintAnomaliesAnalysis.isEnabled()) {
					constraintPropertiesMap.get(constraint).setConstraintFalseOptionalStatus(ConstraintFalseOptionalStatus.NORMAL);
					constraintPropertiesMap.get(constraint).setConstraintDeadStatus(ConstraintDeadStatus.NORMAL);
				}
			}

			// get constraint anomalies
			for (IConstraint constraint : getRedundantConstraints()) {
				constraintPropertiesMap.get(constraint).setConstraintRedundancyStatus(ConstraintRedundancyStatus.REDUNDANT);
			}
			for (IConstraint constraint : getTautologyConstraints()) {
				constraintPropertiesMap.get(constraint).setConstraintRedundancyStatus(ConstraintRedundancyStatus.TAUTOLOGY);
			}
			for (IConstraint constraint : getVoidConstraints()) {
				constraintPropertiesMap.get(constraint).setConstraintSatisfiabilityStatus(ConstraintFalseSatisfiabilityStatus.VOID_MODEL);
			}
			for (IConstraint constraint : getContradictoryConstraints()) {
				constraintPropertiesMap.get(constraint).setConstraintSatisfiabilityStatus(ConstraintFalseSatisfiabilityStatus.UNSATISFIABLE);
			}
			for (IConstraint constraint : getAnomalyConstraints()) {
				final ConstraintProperties constraintProperties = constraintPropertiesMap.get(constraint);
				if (!constraintProperties.getDeadFeatures().isEmpty()) {
					constraintProperties.setConstraintDeadStatus(ConstraintDeadStatus.DEAD);
				}
				if (!constraintProperties.getFalseOptionalFeatures().isEmpty()) {
					constraintProperties.setConstraintFalseOptionalStatus(ConstraintFalseOptionalStatus.FALSE_OPTIONAL);
				}
			}
		}
	}

	public void updateFeatures() {
		updateFeatures(null);
	}

	public void updateFeatures(IMonitor monitor) {
		if (calculateFeatures) {
			if (monitor == null) {
				monitor = new NullMonitor();
			}
			// set default values for feature properties
			for (IFeature feature : featureModel.getFeatures()) {
				featurePropertiesMap.get(feature).setFeatureSelectionStatus(FeatureSelectionStatus.COMMON);
				featurePropertiesMap.get(feature).setFeatureDeterminedStatus(FeatureDeterminedStatus.UNKNOWN);

				final IFeatureStructure structure = feature.getStructure();
				final IFeatureStructure parent = structure.getParent();
				if (parent == null) {
					featurePropertiesMap.get(feature).setFeatureParentStatus(FeatureParentStatus.MANDATORY);
				} else {
					if (parent.isAnd()) {
						if (structure.isMandatorySet()) {
							featurePropertiesMap.get(feature).setFeatureParentStatus(FeatureParentStatus.MANDATORY);
						} else {
							featurePropertiesMap.get(feature).setFeatureParentStatus(FeatureParentStatus.OPTIONAL);
						}
					} else {
						featurePropertiesMap.get(feature).setFeatureParentStatus(FeatureParentStatus.GROUP);
					}
				}
			}

			// get feature anomalies
			for (IFeature feature : getDeadFeatures()) {
				featurePropertiesMap.get(feature).setFeatureSelectionStatus(FeatureSelectionStatus.DEAD);
			}
			for (IFeature feature : getFalseOptionalFeatures()) {
				featurePropertiesMap.get(feature).setFeatureParentStatus(FeatureParentStatus.FALSE_OPTIONAL);
			}
			for (IFeature feature : getIndeterminedHiddenFeatures()) {
				featurePropertiesMap.get(feature).setFeatureDeterminedStatus(FeatureDeterminedStatus.INDETERMINATE_HIDDEN);
			}
		}
	}

	// TODO implement as analysis
	public int countConcreteFeatures() {
		int number = 0;
		for (IFeature feature : featureModel.getFeatures()) {
			if (feature.getStructure().isConcrete()) {
				number++;
			}
		}
		return number;
	}

	// TODO implement as analysis
	public int countHiddenFeatures() {
		int number = 0;
		for (IFeature feature : featureModel.getFeatures()) {
			final IFeatureStructure structure = feature.getStructure();
			if (structure.isHidden() || structure.hasHiddenParent()) {
				number++;
			}
		}
		return number;
	}

	// TODO implement as analysis
	public int countTerminalFeatures() {
		int number = 0;
		for (IFeature feature : featureModel.getFeatures()) {
			if (!feature.getStructure().hasChildren()) {
				number++;
			}
		}
		return number;
	}

	/**
	 * Returns an explanation why the given feature model element is defect or null if it cannot be explained.
	 * 
	 * @param modelElement potentially defect feature model element
	 * @return an explanation why the given feature model element is defect or null if it cannot be explained
	 */
	public Explanation getExplanation(IFeatureModelElement modelElement) {
		return getExplanation(modelElement, null);
	}

	/**
	 * Returns an explanation why the given feature model element is defect or null if it cannot be explained.
	 * 
	 * @param modelElement potentially defect feature model element
	 * @param context another feature model that is used as reference for the explanations
	 * @return an explanation why the given feature model element is defect or null if it cannot be explained
	 */
	@CheckForNull
	public Explanation getExplanation(IFeatureModelElement modelElement, FeatureModelFormula context) {
		if (modelElement instanceof IFeature) {
			return getFeatureExplanation((IFeature) modelElement, context);
		} else if (modelElement instanceof IConstraint) {
			return getConstraintExplanation((IConstraint) modelElement, context);
		}
		return null;
	}

	/**
	 * Returns an explanation why the given constraint is defect or null if it cannot be explained.
	 * 
	 * @param constraint potentially defect constraint
	 * @return an explanation why the given constraint is defect or null if it cannot be explained
	 */
	public Explanation getConstraintExplanation(IConstraint constraint, FeatureModelFormula context) {
		synchronized (constraint) {
			Explanation explanation = null;
			final ConstraintProperties constraintProperties = constraintPropertiesMap.get(constraint);

			if (constraintProperties != null) {
				switch (constraintProperties.getConstraintRedundancyStatus()) {
				case REDUNDANT:
				case TAUTOLOGY:
					break;
				case IMPLICIT:
					explanation = constraintProperties.getRedundantExplanation();
					if (explanation != null) {
						// TODO use context
						explanation = createExplanation(redundantConstraintExplanationCreator, constraint, context);
						constraintProperties.setRedundantExplanation(explanation);
					}
					break;
				default:
					break;
				}
			}
			return explanation;
		}
	}

	/**
	 * Returns an explanation why the given feature is defect or null if it cannot be explained.
	 * 
	 * @param feature potentially defect feature
	 * @return an explanation why the given feature is defect or null if it cannot be explained
	 */
	public Explanation getFeatureExplanation(IFeature feature, FeatureModelFormula context) {
		synchronized (feature) {
			Explanation explanation = null;
			final FeatureProperties featureProperties = featurePropertiesMap.get(feature);
			if (featureProperties != null) {
				switch (featureProperties.getFeatureSelectionStatus()) {
				case DEAD:
					explanation = featureProperties.getDeadExplanation();
					if (explanation != null) {
						explanation = createExplanation(deadFeatureExplanationCreator, feature, context);
						featureProperties.setDeadExplanation(explanation);
					}
					break;
				default:
					break;
				}
				switch (featureProperties.getFeatureParentStatus()) {
				case FALSE_OPTIONAL:
					explanation = featureProperties.getFalseOptionalExplanation();
					if (explanation != null) {
						explanation = createExplanation(falseOptionalFeatureExplanationCreator, feature, context);
						featureProperties.setFalseOptionalExplanation(explanation);
					}
					break;
				default:
					break;
				}
			}
			return explanation;
		}
	}

	private <D extends IFeatureModelElement> Explanation createExplanation(ExplanationCreator creator, D element, FeatureModelFormula formula) {
		return creator.getExplanation();
	}

	/**
	 * <p>
	 * Returns whether the conjunction of A always implies the disjunction of B in the current feature model.
	 * </p>
	 * 
	 * <p>
	 * In other words, the following satisfiability query is checked:
	 * 
	 * <pre>
	 * TAUT(FM &rArr; ((&and;<sub>a&in;A</sub> a) &rArr; (&or;<sub>b&in;B</sub> b)))
	 * </pre>
	 * </p>
	 * 
	 * <p>
	 * Note that this formula is always true if B is empty.
	 * </p>
	 * 
	 * @param a set of features that form a conjunction
	 * @param b set of features that form a disjunction
	 * @return whether the conjunction of A always implies the disjunction of B in the current feature model
	 * @throws TimeoutException
	 * 
	 * @deprecated Use ConfigurationPropagator instead.
	 */
	@Deprecated
	public boolean checkImplies(Collection<IFeature> a, Collection<IFeature> b) {
		if (b.isEmpty()) {
			return true;
		}

		final CNF cnf = formula.getCNF();
		final IVariables variables = cnf.getVariables();

		// (A1 and ... or An) => (B1 or ... or Bm)
		// 	 |= -A1 or ... or -An or B1 or ... or Bm
		//   |= -(A1 and ... and An and -B1 and ... and -Bm)
		final int[] literals = new int[a.size() + b.size()];
		int index = 0;
		for (IFeature feature : b) {
			literals[index++] = -variables.getVariable(feature.getName());
		}
		for (IFeature feature : a) {
			literals[index++] = variables.getVariable(feature.getName());
		}

		final HasSolutionAnalysis analysis = new HasSolutionAnalysis(cnf);
		analysis.setAssumptions(new LiteralSet(literals));

		return LongRunningWrapper.runMethod(analysis);
	}

	/**
	 * @deprecated Use ConfigurationPropagator instead.
	 */
	@Deprecated
	public boolean checkIfFeatureCombinationPossible(IFeature feature1, Collection<IFeature> dependingFeatures) {
		if (dependingFeatures.isEmpty()) {
			return true;
		}

		final CNF cnf = formula.getCNF();
		final IVariables variables = cnf.getVariables();

		final CoreDeadAnalysis analysis = new CoreDeadAnalysis(cnf);
		analysis.setAssumptions(new LiteralSet(variables.getVariable(feature1.getName())));
		final LiteralSet result = LongRunningWrapper.runMethod(analysis);

		final LiteralSet dependingVariables = variables.convertToVariables(Functional.mapToList(dependingFeatures, FeatureUtils.GET_FEATURE_NAME), false);
		final LiteralSet negativeVariables = result.retainAll(dependingVariables);
		return negativeVariables.isEmpty();
	}

	public boolean isCalculateFeatures() {
		return calculateFeatures;
	}

	public void setCalculateFeatures(boolean calculateFeatures) {
		this.calculateFeatures = calculateFeatures;
	}

	public boolean isCalculateConstraints() {
		return calculateConstraints;
	}

	public void setCalculateConstraints(boolean calculateConstraints) {
		this.calculateConstraints = calculateConstraints;
	}

	public boolean isCalculateRedundantConstraints() {
		return constraintRedundancyAnalysis.isEnabled();
	}

	/**
	 * Defines whether redundant constraints should be calculated.
	 */
	public void setCalculateRedundantConstraints(boolean calculateRedundantConstraints) {
		constraintRedundancyAnalysis.setEnabled(calculateRedundantConstraints);
	}

	public boolean isCalculateTautologyConstraints() {
		return constraintTautologyAnalysis.isEnabled();
	}

	/**
	 * Defines whether constraints that are tautologies should be calculated.
	 */
	public void setCalculateTautologyConstraints(boolean calculateTautologyConstraints) {
		constraintTautologyAnalysis.setEnabled(calculateTautologyConstraints);
		if (calculateTautologyConstraints) {
			constraintRedundancyAnalysis.setEnabled(true);
		}
	}

	public boolean isCalculateFOConstraints() {
		return constraintAnomaliesAnalysis.isEnabled();
	}

	public void setCalculateFOConstraints(boolean calculateFOConstraints) {
		constraintAnomaliesAnalysis.setEnabled(calculateFOConstraints);
	}

	public boolean isCalculateDeadConstraints() {
		return constraintAnomaliesAnalysis.isEnabled();
	}

	public void setCalculateDeadConstraints(boolean calculateDeadConstraints) {
		constraintAnomaliesAnalysis.setEnabled(calculateDeadConstraints);
	}

	public boolean isRunCalculationAutomatically() {
		return runCalculationAutomatically;
	}

	public void setRunCalculationAutomatically(boolean runCalculationAutomatically) {
		this.runCalculationAutomatically = runCalculationAutomatically;
	}

	/**
	 * Returns an explanation why the feature model is void.
	 * That is the same explanation for why its root feature is dead.
	 * 
	 * @return an explanation; null if it cannot be explained
	 */
	public Explanation getVoidFeatureModelExplanation() {
		return getVoidFeatureModelExplanation(featureModel);
	}

	/**
	 * Returns an explanation why the given feature model is void.
	 * That is the same explanation for why its root feature is dead.
	 * 
	 * @param fm potentially void feature model; not null
	 * @return an explanation; null if it cannot be explained
	 */
	public Explanation getVoidFeatureModelExplanation(IFeatureModel fm) {
		return getDeadFeatureExplanation(fm, FeatureUtils.getRoot(fm));
	}

	/**
	 * Returns an explanation why the given feature is dead.
	 * 
	 * @param feature potentially dead feature; not null
	 * @return an explanation; null if it cannot be explained
	 */
	public Explanation getDeadFeatureExplanation(IFeature feature) {
		return getDeadFeatureExplanation(featureModel, feature);
	}

	/**
	 * Adds an explanation why the given feature is dead.
	 * 
	 * @param fm feature model containing the feature; not null
	 * @param feature potentially dead feature; not null
	 * @return an explanation; null if it cannot be explained
	 */
	public Explanation getDeadFeatureExplanation(IFeatureModel fm, IFeature feature) {
		if (!deadFeatureExplanations.containsKey(feature)) {
			addDeadFeatureExplanation(fm, feature);
		}
		return deadFeatureExplanations.get(feature);
	}

	/**
	 * Adds an explanation why the given feature is dead.
	 * 
	 * @param fm feature model containing the feature; not null
	 * @param feature potentially dead feature; not null
	 */
	private void addDeadFeatureExplanation(IFeatureModel fm, IFeature feature) {
		final DeadFeatureExplanationCreator creator = fm == this.featureModel ? deadFeatureExplanationCreator
				: explanationCreatorFactory.getDeadFeatureExplanationCreator(fm);
		creator.setDeadFeature(feature);
		deadFeatureExplanations.put(feature, creator.getExplanation());
	}

	/**
	 * Returns an explanation why the given feature is false-optional.
	 * 
	 * @param feature potentially false-optional feature; not null
	 * @return an explanation; null if it cannot be explained
	 */
	public Explanation getFalseOptionalFeatureExplanation(IFeature feature) {
		return getFalseOptionalFeatureExplanation(featureModel, feature);
	}

	/**
	 * Returns an explanation why the given feature is false-optional.
	 * 
	 * @param fm feature model containing the feature; not null
	 * @param feature potentially false-optional feature; not null
	 * @return an explanation; null if it cannot be explained
	 */
	public Explanation getFalseOptionalFeatureExplanation(IFeatureModel fm, IFeature feature) {
		if (!falseOptionalFeatureExplanations.containsKey(feature)) {
			addFalseOptionalFeatureExplanation(fm, feature);
		}
		return falseOptionalFeatureExplanations.get(feature);
	}

	/**
	 * Adds an explanation why the given feature is false-optional.
	 * 
	 * @param fm feature model containing the feature; not null
	 * @param feature potentially false-optional feature; not null
	 */
	private void addFalseOptionalFeatureExplanation(IFeatureModel fm, IFeature feature) {
		final FalseOptionalFeatureExplanationCreator creator = fm == this.featureModel ? falseOptionalFeatureExplanationCreator
				: explanationCreatorFactory.getFalseOptionalFeatureExplanationCreator(fm);
		creator.setFalseOptionalFeature(feature);
		falseOptionalFeatureExplanations.put(feature, creator.getExplanation());
	}

	/**
	 * Returns an explanation why the given constraint is redundant.
	 * 
	 * @param constraint potentially redundant constraint; not null
	 * @return an explanation; null if it cannot be explained
	 */
	public Explanation getRedundantConstraintExplanation(IConstraint constraint) {
		return getRedundantConstraintExplanation(featureModel, constraint);
	}

	/**
	 * Returns an explanation why the given constraint is redundant.
	 * 
	 * @param constraint potentially redundant constraint; not null
	 * @return an explanation; null if it cannot be explained
	 */
	public Explanation getRedundantConstraintExplanation(IFeatureModel fm, IConstraint constraint) {
		if (!redundantConstraintExplanations.containsKey(constraint)) {
			addRedundantConstraintExplanation(fm, constraint);
		}
		return redundantConstraintExplanations.get(constraint);
	}

	/**
	 * <p>
	 * Adds an explanation why the given constraint is redundant.
	 * </p>
	 * 
	 * <p>
	 * Uses the given feature model, which may differ from the default feature model stored in this instance.
	 * This is for example the case when explaining implicit constraints in subtree models.
	 * </p>
	 * 
	 * @param fm feature model containing the constraint; not null
	 * @param constraint potentially redundant constraint; not null
	 */
	private void addRedundantConstraintExplanation(IFeatureModel fm, IConstraint constraint) {
		final RedundantConstraintExplanationCreator creator = fm == this.featureModel ? redundantConstraintExplanationCreator
				: explanationCreatorFactory.getRedundantConstraintExplanationCreator(fm);
		creator.setRedundantConstraint(constraint);
		redundantConstraintExplanations.put(constraint, creator.getExplanation());
	}

	/**
	 * Clears all explanations.
	 */
	public void clearExplanations() {
		deadFeatureExplanations.clear();
		falseOptionalFeatureExplanations.clear();
		redundantConstraintExplanations.clear();
		deadFeatureExplanationCreator.setFeatureModel(featureModel);
		falseOptionalFeatureExplanationCreator.setFeatureModel(featureModel);
		redundantConstraintExplanationCreator.setFeatureModel(featureModel);
	}
}
