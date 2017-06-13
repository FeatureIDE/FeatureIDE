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
import de.ovgu.featureide.fm.core.analysis.cnf.FeatureModelCNF;
import de.ovgu.featureide.fm.core.analysis.cnf.FeatureModelFormula;
import de.ovgu.featureide.fm.core.analysis.cnf.IVariables;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.Nodes;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.AbstractAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.AnalysisResult;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.AtomicSetAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.CauseAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.ContradictionAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.CoreDeadAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.HasSolutionAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.IndependentContradictionAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.IndependentRedundancyAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.IndeterminedAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.RedundancyAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.CauseAnalysis.Anomalies;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.AdvancedSatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISimpleSatSolver.SatResult;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.explanations.DeadFeatureExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.FalseOptionalFeatureExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.RedundantConstraintExplanationCreator;
import de.ovgu.featureide.fm.core.filter.FeatureSetFilter;
import de.ovgu.featureide.fm.core.filter.HiddenFeatureFilter;
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

public class FeatureModelAnalyzer {

	private static class AnalysisWrapper<R, A extends AbstractAnalysis<R>> {

		private final Class<A> analysis;

		private Object syncObject = new Object();
		private IMonitor monitor = new NullMonitor();
		private boolean enabled = true;

		private AnalysisResult<R> analysisResult;

		public AnalysisWrapper(Class<A> analysis) {
			this.analysis = analysis;
		}

		public R getCachedResult() {
			synchronized (this) {
				return analysisResult == null ? null : analysisResult.getResult();
			}
		}

		public A createNewAnalysis(CNF cnf) {
			try {
				return analysis.getConstructor(CNF.class).newInstance(cnf);
			} catch (InstantiationException | IllegalAccessException | IllegalArgumentException | InvocationTargetException | NoSuchMethodException
					| SecurityException e) {
				throw new AssertionError();
			}
		}

		public R getResult(CNF cnf) {
			return getResult(createNewAnalysis(cnf));
		}

		public R getResult(A analysisInstance) {
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

	/**
	 * Defines whether features should be included into calculations.
	 * If features are not analyzed, then constraints a also NOT analyzed.
	 */
	public boolean calculateFeatures = true;
	/**
	 * Defines whether constraints should be included into calculations.
	 */
	public boolean calculateConstraints = true;
	/**
	 * Defines whether redundant constraints should be calculated.
	 */
	public boolean calculateRedundantConstraints = true;
	/**
	 * Defines whether constraints that are tautologies should be calculated.
	 */
	public boolean calculateTautologyConstraints = true;

	public boolean calculateFOConstraints = true;

	public boolean calculateDeadConstraints = true;
	/**
	 * Defines whether analysis should be performed automatically.
	 */
	public boolean runCalculationAutomatically = true;

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

	/**
	 * Creates explanations for dead features.
	 * Stored for performance so the underlying CNF is not recreated for every explanation.
	 */
	private final DeadFeatureExplanationCreator deadFeatureExplanationCreator;
	/**
	 * Creates explanations for false-optional features.
	 * Stored for performance so the underlying CNF is not recreated for every explanation.
	 */
	private final FalseOptionalFeatureExplanationCreator falseOptionalFeatureExplanationCreator;
	/**
	 * Creates explanations for redundant constraints.
	 * Stored for performance so the underlying CNF is not recreated for every explanation.
	 */
	private final RedundantConstraintExplanationCreator redundantConstraintExplanationCreator;

	private final FeatureModelFormula formula;
	private final IFeatureModel featureModel;
	private final List<IConstraint> constraints;

	private final int[] clauseGroupSize;
	private final List<LiteralSet> constraintClauses;

	private final AnalysisWrapper<Boolean, HasSolutionAnalysis> validAnalysis = new AnalysisWrapper<>(HasSolutionAnalysis.class);
	private final AnalysisWrapper<List<LiteralSet>, AtomicSetAnalysis> atomicSetAnalysis = new AnalysisWrapper<>(AtomicSetAnalysis.class);
	private final AnalysisWrapper<LiteralSet, CoreDeadAnalysis> coreDeadAnalysis = new AnalysisWrapper<>(CoreDeadAnalysis.class);
	private final AnalysisWrapper<List<LiteralSet>, IndependentRedundancyAnalysis> foAnalysis = new AnalysisWrapper<>(IndependentRedundancyAnalysis.class);
	private final AnalysisWrapper<LiteralSet, IndeterminedAnalysis> determinedAnalysis = new AnalysisWrapper<>(IndeterminedAnalysis.class);
	private final AnalysisWrapper<List<LiteralSet>, RedundancyAnalysis> constraintRedundancyAnalysis = new AnalysisWrapper<>(RedundancyAnalysis.class);
	private final AnalysisWrapper<List<LiteralSet>, IndependentRedundancyAnalysis> constraintTautologyAnalysis = new AnalysisWrapper<>(
			IndependentRedundancyAnalysis.class);
	private final AnalysisWrapper<List<Anomalies>, CauseAnalysis> constraintAnomaliesAnalysis = new AnalysisWrapper<>(CauseAnalysis.class);
	private final AnalysisWrapper<List<LiteralSet>, IndependentContradictionAnalysis> constraintContradictionAnalysis = new AnalysisWrapper<>(
			IndependentContradictionAnalysis.class);
	private final AnalysisWrapper<List<LiteralSet>, ContradictionAnalysis> constraintVoidAnalysis = new AnalysisWrapper<>(ContradictionAnalysis.class);

	private final List<AnalysisWrapper<?, ? extends AbstractAnalysis<? extends Object>>> list = Arrays.asList(validAnalysis, atomicSetAnalysis,
			coreDeadAnalysis, foAnalysis, determinedAnalysis, constraintContradictionAnalysis, constraintVoidAnalysis, constraintTautologyAnalysis,
			constraintRedundancyAnalysis, constraintAnomaliesAnalysis);

	public void reset() {
		for (AnalysisWrapper<?, ?> analysisWrapper : list) {
			analysisWrapper.reset();
		}
		init();
	}

	private void init() {
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
	}

	public FeatureModelAnalyzer(FeatureModelFormula formula, IFeatureModel featureModel) {
		this.formula = formula;
		this.featureModel = featureModel;

		featurePropertiesMap = new HashMap<>();
		constraintPropertiesMap = new HashMap<>();
		elementPropertiesMap = new HashMap<>();

		deadFeatureExplanationCreator = new DeadFeatureExplanationCreator(featureModel);
		falseOptionalFeatureExplanationCreator = new FalseOptionalFeatureExplanationCreator(featureModel);
		redundantConstraintExplanationCreator = new RedundantConstraintExplanationCreator(featureModel);

		constraints = featureModel.getConstraints();
		constraintClauses = new ArrayList<>();
		clauseGroupSize = getClauseGroups(constraints, constraintClauses);

		init();
	}

	protected int[] getClauseGroups(List<IConstraint> constraints, List<LiteralSet> constraintClauses) {
		int[] clauseGroupSize = new int[constraints.size()];
		final IVariables variables = formula.getEmptyCNF().getVariables();
		int i = 0;
		for (IConstraint constraint : constraints) {
			final List<LiteralSet> clauses = Nodes.convert(variables, constraint.getNode());
			constraintClauses.addAll(clauses);
			clauseGroupSize[i++] = clauses.size();
		}
		return clauseGroupSize;
	}

	public FeatureModelAnalyzer(IFeatureModel featureModel) {
		this(new FeatureModelFormula(featureModel), featureModel);
	}

	public FeatureModelAnalyzer(FeatureModelFormula formula) {
		this(formula, formula.getFeatureModel());
	}

	public boolean isValid() {
		final Boolean result = validAnalysis.getResult(formula.getCNF());
		return result == null ? false : result;
	}

	public List<IFeature> getCoreFeatures() {
		final FeatureModelCNF cnf = formula.getCNF();
		final LiteralSet result = coreDeadAnalysis.getResult(cnf);
		if (result == null) {
			return Collections.emptyList();
		}
		return Functional.mapToList(cnf.getVariables().convertToString(result, true, false, false), new StringToFeature(featureModel));
	}

	public List<IFeature> getDeadFeatures() {
		final FeatureModelCNF cnf = formula.getCNF();
		final LiteralSet result = coreDeadAnalysis.getResult(cnf);
		if (result == null) {
			return Collections.emptyList();
		}
		return Functional.mapToList(cnf.getVariables().convertToString(result, false, true, false), new StringToFeature(featureModel));
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
		final FeatureModelCNF cnf = formula.getCNF();
		final LiteralSet result = coreDeadAnalysis.getResult(cnf);
		if (result == null) {
			return Collections.emptyList();
		}
		final Set<IFeature> uncommonFeatures = Functional
				.toSet(Functional.map(cnf.getVariables().convertToString(result, true, true, false), new StringToFeature(featureModel)));
		return Functional.mapToList(featureModel.getFeatures(), new InverseFilter<>(new FeatureSetFilter(uncommonFeatures)),
				new Functional.IdentityFunction<IFeature>());
	}

	public List<List<IFeature>> getAtomicSets() {
		final FeatureModelCNF cnf = formula.getCNF();
		final List<LiteralSet> result = atomicSetAnalysis.getResult(cnf);
		if (result == null) {
			return Collections.emptyList();
		}

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
		final FeatureModelCNF cnf = formula.getCNF();
		LiteralSet result = determinedAnalysis.getCachedResult();
		if (result == null) {
			final IndeterminedAnalysis analysis = determinedAnalysis.createNewAnalysis(cnf);
			final LiteralSet convertToVariables = cnf.getVariables()
					.convertToVariables(Functional.mapToList(featureModel.getFeatures(), new HiddenFeatureFilter(), FeatureUtils.GET_FEATURE_NAME));
			analysis.setVariables(convertToVariables);
			result = determinedAnalysis.getResult(analysis);
			if (result == null) {
				return Collections.emptyList();
			}
		}
		return Functional.mapToList(cnf.getVariables().convertToString(result, true, false, false), new StringToFeature(featureModel));
	}

	public List<IFeature> getFalseOptionalFeatures() {
		final List<IFeature> optionalFeatures = Functional.filterToList(featureModel.getFeatures(), new OptionalFeatureFilter());
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
		List<LiteralSet> result = foAnalysis.getCachedResult();
		if (result == null) {
			final FeatureModelCNF cnf = formula.getCNF();
			final IVariables variables = cnf.getVariables();
			final IndependentRedundancyAnalysis analysis = foAnalysis.createNewAnalysis(cnf);

			final List<LiteralSet> literalSetList = new ArrayList<>();
			for (IFeature iFeature : optionalFeatures) {
				literalSetList.add(new LiteralSet(variables.getVariable(FeatureUtils.getParent(iFeature).getName(), false),
						variables.getVariable(iFeature.getName(), true)));
			}
			analysis.setClauseList(literalSetList);
			result = foAnalysis.getResult(analysis);
			if (result == null) {
				return Collections.emptyList();
			}
		}
		return result;
	}

	public List<IConstraint> getContradictoryConstraints() {
		final List<IConstraint> constraints = getVoidConstraints();
		final ArrayList<LiteralSet> constraintClauses = new ArrayList<>();
		final int[] clauseGroupSize = getClauseGroups(constraints, constraintClauses);

		List<LiteralSet> result = constraintContradictionAnalysis.getCachedResult();
		if (result == null) {
			final IndependentContradictionAnalysis analysis = constraintContradictionAnalysis.createNewAnalysis(formula.getEmptyCNF());

			analysis.setClauseList(constraintClauses);
			analysis.setClauseGroupSize(clauseGroupSize);
			result = constraintContradictionAnalysis.getResult(analysis);
			if (result == null) {
				return Collections.emptyList();
			}
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
		List<LiteralSet> result = constraintVoidAnalysis.getCachedResult();
		if (result == null) {
			final ContradictionAnalysis analysis = constraintVoidAnalysis.createNewAnalysis(formula.getFeatureTreeClauses());

			analysis.setClauseList(constraintClauses);
			analysis.setClauseGroupSize(clauseGroupSize);
			result = constraintVoidAnalysis.getResult(analysis);
			if (result == null) {
				return Collections.emptyList();
			}
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
		final FeatureModelCNF cnf = formula.getCNF();

		List<Anomalies> result = constraintAnomaliesAnalysis.getCachedResult();
		if (result == null) {
			final CauseAnalysis analysis = constraintAnomaliesAnalysis.createNewAnalysis(formula.getFeatureTreeClauses());
			final Anomalies initialAnomalies = new Anomalies();
			initialAnomalies.setDeadVariables(coreDeadAnalysis.getResult(cnf));
			initialAnomalies.setRedundantClauses(
					Functional.removeNull(getFalseOptionalFeatures(Functional.filterToList(featureModel.getFeatures(), new OptionalFeatureFilter()))));
			analysis.setAnomalies(initialAnomalies);
			analysis.setClauseList(constraintClauses);
			analysis.setClauseGroupSize(clauseGroupSize);
			result = constraintAnomaliesAnalysis.getResult(analysis);
			if (result == null) {
				return Collections.emptyList();
			}
		}

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

		List<LiteralSet> result = constraintTautologyAnalysis.getCachedResult();
		if (result == null) {
			final IndependentRedundancyAnalysis analysis = constraintTautologyAnalysis.createNewAnalysis(formula.getEmptyCNF());

			analysis.setClauseList(constraintClauses);
			analysis.setClauseGroupSize(clauseGroupSize);
			result = constraintTautologyAnalysis.getResult(analysis);
			if (result == null) {
				return Collections.emptyList();
			}
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
		List<LiteralSet> result = constraintRedundancyAnalysis.getCachedResult();
		if (result == null) {
			final RedundancyAnalysis analysis = constraintRedundancyAnalysis.createNewAnalysis(formula.getFeatureTreeClauses());

			analysis.setClauseList(constraintClauses);
			analysis.setClauseGroupSize(clauseGroupSize);
			result = constraintRedundancyAnalysis.getResult(analysis);
			if (result == null) {
				return Collections.emptyList();
			}
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
		updateFeatures();

		updateConstraints();

		return elementPropertiesMap;
	}

	public void updateConstraints() {
		// set default values for constraint properties
		for (IConstraint constraint : featureModel.getConstraints()) {
			constraintPropertiesMap.get(constraint).setConstraintRedundancyStatus(ConstraintRedundancyStatus.NORMAL);
			constraintPropertiesMap.get(constraint).setConstraintSatisfiabilityStatus(ConstraintFalseSatisfiabilityStatus.SATISFIABLE);
			constraintPropertiesMap.get(constraint).setConstraintFalseOptionalStatus(ConstraintFalseOptionalStatus.NORMAL);
			constraintPropertiesMap.get(constraint).setConstraintDeadStatus(ConstraintDeadStatus.NORMAL);
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
		//		for (IConstraint constraint : getFalseOptionalConstraints()) {
		//			constraintPropertiesMap.get(constraint).setConstraintFalseOptionalStatus(ConstraintFalseOptionalStatus.FALSE_OPTIONAL);
		//		}
		//		for (IConstraint constraint : getDeadConstraints()) {
		//			constraintPropertiesMap.get(constraint).setConstraintDeadStatus(ConstraintDeadStatus.DEAD);
		//		}
	}

	public void updateFeatures() {
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
	 * Sets the cancel status of analysis.<br>
	 * <code>true</code> if analysis should be stopped.
	 */
	public void cancel(boolean value) {
		//		cancel = value;
		reset();
	}

	/**
	 * Returns an explanation why the given feature model element is defect or null if it cannot be explained.
	 * 
	 * @param modelElement potentially defect feature model element
	 * @return an explanation why the given feature model element is defect or null if it cannot be explained
	 */
	public Explanation getExplanation(IFeatureModelElement modelElement) {
		Explanation explanation = null;
		if (modelElement instanceof IFeature) {
			final FeatureProperties featureProperties = featurePropertiesMap.get(modelElement);
			if (featureProperties != null) {
				final IFeature feature = (IFeature) modelElement;
				switch (featureProperties.getFeatureSelectionStatus()) {
				case DEAD:
					explanation = featureProperties.getDeadExplanation();
					if (explanation != null) {
						deadFeatureExplanationCreator.setDeadFeature(feature);
						explanation = deadFeatureExplanationCreator.getExplanation();
						featureProperties.setFalseOptionalExplanation(explanation);
					}
					break;
				default:
					break;
				}
				switch (featureProperties.getFeatureParentStatus()) {
				case FALSE_OPTIONAL:
					explanation = featureProperties.getFalseOptionalExplanation();
					if (explanation != null) {
						falseOptionalFeatureExplanationCreator.setFalseOptionalFeature(feature);
						explanation = falseOptionalFeatureExplanationCreator.getExplanation();
						featureProperties.setFalseOptionalExplanation(explanation);
					}
					break;
				default:
					break;
				}
			}
		} else if (modelElement instanceof IConstraint) {
			final ConstraintProperties constraintProperties = constraintPropertiesMap.get(modelElement);

			if (constraintProperties != null) {
				final IConstraint constraint = (IConstraint) modelElement;
				switch (constraintProperties.getConstraintRedundancyStatus()) {
				case REDUNDANT:
				case TAUTOLOGY:
				case IMPLICIT:
					explanation = constraintProperties.getRedundantExplanation();
					if (explanation != null) {
						redundantConstraintExplanationCreator.setRedundantConstraint(constraint);
						explanation = redundantConstraintExplanationCreator.getExplanation();
						constraintProperties.setRedundantExplanation(explanation);
					}
					break;
				default:
					break;
				}
			}
		}
		return explanation;
	}

	//	private FeatureProperties getFeatureProperties(final IFeature feature) {
	//		synchronized (featurePropertiesMap) {
	//			FeatureProperties featureProperties = featurePropertiesMap.get(feature);
	//		if (featureProperties == null) {
	//			featureProperties = new FeatureProperties(feature);
	//			
	//		}
	//		return featureProperties;
	//		}
	//	}

	//	/**
	//	 * Adds an explanation why the given feature model element is defect.
	//	 * Uses the default feature model stored in this instance.
	//	 * 
	//	 * @param modelElement potentially defect feature model element
	//	 */
	//	public void addExplanation(IFeatureModelElement modelElement) {
	//
	//		if (modelElement instanceof IFeature) {
	//			final IFeature feature = (IFeature) modelElement;
	//			switch (feature.getProperty().getFeatureStatus()) {
	//			case DEAD:
	//				addDeadFeatureExplanation(fm, feature);
	//				break;
	//			case FALSE_OPTIONAL:
	//				addFalseOptionalFeatureExplanation(fm, feature);
	//				break;
	//			default:
	//				break;
	//			}
	//		} else if (modelElement instanceof IConstraint) {
	//			final IConstraint constraint = (IConstraint) modelElement;
	//			switch (constraint.getConstraintAttribute()) {
	//			case REDUNDANT:
	//			case TAUTOLOGY:
	//			case IMPLICIT:
	//				addRedundantConstraintExplanation(fm, constraint);
	//				break;
	//			default:
	//				break;
	//			}
	//		}
	//	}
	//
	//	/**
	//	 * Returns an explanation why the given feature is dead or null if it cannot be explained.
	//	 * 
	//	 * @param feature potentially dead feature
	//	 * @return an explanation why the given feature is dead or null if it cannot be explained
	//	 */
	//	public Explanation getDeadFeatureExplanation(IFeature feature) {
	//		return deadFeatureExplanations.get(feature);
	//	}
	//
	//	/**
	//	 * Adds an explanation why the given feature is dead.
	//	 * Uses the default feature model stored in this instance.
	//	 * 
	//	 * @param feature potentially dead feature
	//	 */
	//	public void addDeadFeatureExplanation(IFeature feature) {
	//		addDeadFeatureExplanation(fm, feature);
	//	}
	//
	//	/**
	//	 * Adds an explanation why the given feature is dead.
	//	 * Uses the given feature model, which may differ from the default feature model stored in this instance.
	//	 * 
	//	 * @param fm feature model containing the feature
	//	 * @param feature potentially dead feature
	//	 */
	//	public void addDeadFeatureExplanation(IFeatureModel fm, IFeature feature) {
	//		final DeadFeatureExplanationCreator creator = fm == this.fm ? deadFeatureExplanationCreator : new DeadFeatureExplanationCreator(fm);
	//		creator.setDeadFeature(feature);
	//		deadFeatureExplanations.put(feature, creator.getExplanation());
	//	}
	//
	//	/**
	//	 * Returns an explanation why the given feature is false-optional or null if it cannot be explained.
	//	 * 
	//	 * @param feature potentially false-optional feature
	//	 * @return an explanation why the given feature is false-optional or null if it cannot be explained
	//	 */
	//	public Explanation getFalseOptionalFeatureExplanation(IFeature feature) {
	//		return falseOptionalFeatureExplanations.get(feature);
	//	}
	//
	//	/**
	//	 * Adds an explanation why the given feature is false-optional.
	//	 * Uses the default feature model stored in this instance.
	//	 * 
	//	 * @param feature potentially false-optional feature
	//	 */
	//	public void addFalseOptionalFeatureExplanation(IFeature feature) {
	//		addFalseOptionalFeatureExplanation(fm, feature);
	//	}
	//
	//	/**
	//	 * Adds an explanation why the given feature is false-optional.
	//	 * Uses the given feature model, which may differ from the default feature model stored in this instance.
	//	 * 
	//	 * @param fm feature model containing the feature
	//	 * @param feature potentially false-optional feature
	//	 */
	//	public void addFalseOptionalFeatureExplanation(IFeatureModel fm, IFeature feature) {
	//		final FalseOptionalFeatureExplanationCreator creator = fm == this.fm ? falseOptionalFeatureExplanationCreator
	//				: new FalseOptionalFeatureExplanationCreator(fm);
	//		creator.setFalseOptionalFeature(feature);
	//		falseOptionalFeatureExplanations.put(feature, creator.getExplanation());
	//	}
	//
	//	/**
	//	 * Returns an explanation why the given constraint is redundant or null if it cannot be explained.
	//	 * 
	//	 * @param constraint potentially redundant constraint
	//	 * @return an explanation why the given constraint is redundant or null if it cannot be explained
	//	 */
	//	public Explanation getRedundantConstraintExplanation(IConstraint constraint) {
	//		return redundantConstraintExplanations.get(constraint);
	//	}
	//
	//	/**
	//	 * Adds an explanation why the given constraint is redundant.
	//	 * Uses the default feature model stored in this instance.
	//	 * 
	//	 * @param constraint possibly redundant constraint
	//	 */
	//	public void addRedundantConstraintExplanation(IConstraint constraint) {
	//		addRedundantConstraintExplanation(fm, constraint);
	//	}
	//
	//	/**
	//	 * Adds an explanation why the given constraint is redundant.
	//	 * Uses the given feature model, which may differ from the default feature model stored in this instance.
	//	 * This is for example the case when explaining implicit constraints in subtree models.
	//	 * 
	//	 * @param fm feature model containing the constraint
	//	 * @param constraint potentially redundant constraint
	//	 */
	//	public void addRedundantConstraintExplanation(IFeatureModel fm, IConstraint constraint) {
	//		final RedundantConstraintExplanationCreator creator = fm == this.fm ? redundantConstraintExplanationCreator
	//				: new RedundantConstraintExplanationCreator(fm);
	//		creator.setRedundantConstraint(constraint);
	//		redundantConstraintExplanations.put(constraint, creator.getExplanation());
	//	}

	/**
	 * checks whether A implies B for the current feature model.
	 * 
	 * in detail the following condition should be checked whether
	 * 
	 * FM => ((A1 and A2 and ... and An) => (B1 or B2 or ... or Bn))
	 * 
	 * is true for all values
	 * 
	 * @param A
	 *            set of features that form a conjunction
	 * @param B
	 *            set of features that form a conjunction
	 * @return
	 * @throws TimeoutException
	 */
	public boolean checkImplies(Collection<IFeature> a, Collection<IFeature> b) throws TimeoutException {
		if (b.isEmpty()) {
			return true;
		}
		final FeatureModelCNF cnf = formula.getCNF();

		// (A1 and ... An) => (B1 or ... Bm)
		int[] literals = new int[a.size() + b.size()];
		int index = 0;
		for (IFeature feature : a) {
			literals[index++] = cnf.getVariables().getVariable(feature.getName());
		}
		for (IFeature feature : b) {
			literals[index++] = -cnf.getVariables().getVariable(feature.getName());
		}

		final AdvancedSatSolver advancedSatSolver = new AdvancedSatSolver(cnf);
		advancedSatSolver.assignmentPushAll(literals);

		return advancedSatSolver.hasSolution() == SatResult.FALSE;
	}

	//	public boolean checkIfFeatureCombinationNotPossible(IFeature a, Collection<IFeature> b) throws TimeoutException {
	//		if (b.isEmpty())
	//			return true;
	//
	//		Node featureModel = NodeCreator.createNodes(featureModel.clone(null));
	//		boolean notValid = true;
	//		for (IFeature f : b) {
	//			Node node = new And(new And(featureModel, new Literal(NodeCreator.getVariable(f, featureModel.clone(null)))),
	//					new Literal(NodeCreator.getVariable(a, featureModel.clone(null))));
	//			notValid &= !new SatSolver(node, 1000).hasSolution();
	//		}
	//		return notValid;
	//	}
	//
	//	/**
	//	 * checks some condition against the feature model. use only if you know
	//	 * what you are doing!
	//	 * 
	//	 * @return
	//	 * @throws TimeoutException
	//	 */
	//	public boolean checkCondition(Node condition) {
	//		final FeatureModelCNF cnf = formula.getCNF();
	//		return false;
	//	}

}
