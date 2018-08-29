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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.configuration;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.analyses.AbstractAnalysis;
import org.prop4j.analyses.ConditionallyCoreDeadAnalysis;
import org.prop4j.analyses.CountSolutionAnalysis;
import org.prop4j.analyses.CoverAnalysis;
import org.prop4j.analyses.GetSolutionAnalysis;
import org.prop4j.analyses.RedundantAnalysis;
import org.prop4j.analyses.ResolveAnalysis;
import org.prop4j.solver.BasicSolver;
import org.prop4j.solver.ISatSolver.SatResult;
import org.prop4j.solver.SatInstance;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.filter.AbstractFeatureFilter;
import de.ovgu.featureide.fm.core.filter.HiddenFeatureFilter;
import de.ovgu.featureide.fm.core.filter.base.IFilter;
import de.ovgu.featureide.fm.core.filter.base.InverseFilter;
import de.ovgu.featureide.fm.core.filter.base.OrFilter;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.job.IRunner;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor.MethodCancelException;

/**
 * Updates a configuration.
 *
 * @author Sebastian Krieter
 */
public class ConfigurationPropagator implements IConfigurationPropagator {

	public static int FEATURE_LIMIT_FOR_DEFAULT_COMPLETION = 150;

	private static final IFilter<SelectableFeature> manuallySelectedFilter = new IFilter<SelectableFeature>() {
		@Override
		public boolean isValid(SelectableFeature feature) {
			return feature.getManual() != Selection.UNDEFINED;
		}
	};

	private static final IFilter<SelectableFeature> selectedFilter = new IFilter<SelectableFeature>() {
		@Override
		public boolean isValid(SelectableFeature feature) {
			return feature.getSelection() != Selection.UNDEFINED;
		}
	};

	private static final IFilter<SelectableFeature> invalidFeatureFilter = new IFilter<SelectableFeature>() {
		@Override
		public boolean isValid(SelectableFeature feature) {
			return feature.getFeature() != null;
		}
	};

	private static final IFilter<SelectableFeature> concreteFilter = new IFilter<SelectableFeature>() {
		@Override
		public boolean isValid(SelectableFeature feature) {
			return FeatureUtils.isConcrete(feature.getFeature());
		}
	};

	private static final IFilter<SelectableFeature> visibleFilter = new IFilter<SelectableFeature>() {
		@Override
		public boolean isValid(SelectableFeature feature) {
			return !FeatureUtils.hasHiddenParent(feature.getFeature());
		}
	};

	private static Literal getLiteral(final SelectableFeature feature) {
		return new Literal(feature.getFeature().getName(), feature.getSelection() == Selection.SELECTED);
	}

	public class IsValidMethod implements LongRunningMethod<Boolean> {

		private final boolean includeUndefinedFeatures;
		private final boolean includeHiddenFeatures;

		public IsValidMethod(boolean includeUndefinedFeatures, boolean includeHiddenFeatures) {
			this.includeUndefinedFeatures = includeUndefinedFeatures;
			this.includeHiddenFeatures = includeHiddenFeatures;
		}

		@Override
		public Boolean execute(IMonitor monitor) {
			if (rootNode == null) {
				return false;
			}

			final BasicSolver solver;
			try {
				solver = new BasicSolver(rootNode);
			} catch (final ContradictionException e) {
				Logger.logError(e);
				return false;
			}

			Iterable<SelectableFeature> features = getFeatures();
			features = includeHiddenFeatures ? features : Functional.filter(features, visibleFilter);
			features = includeUndefinedFeatures ? features : Functional.filter(features, selectedFilter);
			for (final SelectableFeature feature : features) {
				final int variable = rootNode.getVariable(feature.getFeature().getName());
				solver.assignmentPush((feature.getSelection() == Selection.SELECTED) ? variable : -variable);
			}

			final SatResult satResult = solver.isSatisfiable();
			switch (satResult) {
			case FALSE:
			case TIMEOUT:
				return false;
			case TRUE:
				return true;
			default:
				throw new AssertionError(satResult);
			}
		}
	}

	public class Resolve implements LongRunningMethod<Void> {

		@Override
		public Void execute(IMonitor workMonitor) throws Exception {
			if (rootNode == null) {
				return null;
			}

			configuration.resetAutomaticValues();

			final List<Literal> oldManualSelected = new ArrayList<>();
			for (final SelectableFeature feature : getFeatures(manuallySelectedFilter)) {
				oldManualSelected.add(getLiteral(feature));
				feature.setManual(Selection.UNDEFINED);
			}

			final int[] manualFeatures = LongRunningWrapper.runMethod(new ResolveAnalysis(rootNode, rootNode.convertToInt(oldManualSelected)));
			for (final int feature : manualFeatures) {
				configuration.getSelectablefeature((String) rootNode.getVariableObject(feature))
						.setManual(feature > 0 ? Selection.SELECTED : Selection.UNSELECTED);
			}
			setToAutomatic(manualFeatures, new ConditionallyCoreDeadAnalysis(rootNode));
			setToAutomatic(manualFeatures, new RedundantAnalysis(rootNode));

			return null;
		}

		private void setToAutomatic(final int[] manualFeatures, final AbstractAnalysis<int[]> analysis) {
			analysis.setAssumptions(manualFeatures);
			for (final int feature : LongRunningWrapper.runMethod(analysis)) {
				configuration.setAutomatic(configuration.getSelectablefeature((String) rootNode.getVariableObject(feature)),
						feature > 0 ? Selection.SELECTED : Selection.UNSELECTED);
			}
		}

	}

	public class CountSolutionsMethod implements LongRunningMethod<Long> {

		private final long timeout;
		private final boolean includeHiddenFeatures;

		public CountSolutionsMethod(long timeout, boolean includeHiddenFeatures) {
			this.timeout = timeout;
			this.includeHiddenFeatures = includeHiddenFeatures;
		}

		@Override
		public Long execute(IMonitor monitor) {
			if (rootNode == null) {
				return 0L;
			}
			final List<Literal> definedFeatures = new ArrayList<>();

			Iterable<SelectableFeature> features = getFeatures(selectedFilter);
			features = includeHiddenFeatures ? features : Functional.filter(features, visibleFilter);
			for (final SelectableFeature feature : features) {
				definedFeatures.add(getLiteral(feature));
			}

			final SatInstance node = includeHiddenFeatures ? rootNode : rootNodeWithoutHidden;
			final CountSolutionAnalysis analysis = new CountSolutionAnalysis(node, timeout);
			analysis.setAssumptions(node.convertToInt(definedFeatures));
			final Long result = LongRunningWrapper.runMethod(analysis);
			return result == null ? 0 : result;
		}
	}

	public class FindClause implements LongRunningMethod<List<Node>> {

		private final List<SelectableFeature> featureList;

		public FindClause(List<SelectableFeature> featureList) {
			this.featureList = featureList;
		}

		@Override
		public List<Node> execute(IMonitor workMonitor) {
			if (rootNode == null) {
				return Collections.emptyList();
			}
			final boolean[] results = new boolean[featureList.size()];
			final List<Node> openClauses = new ArrayList<>();

			final Map<String, Boolean> featureMap = new HashMap<String, Boolean>(configuration.features.size() << 1);
			for (final SelectableFeature selectableFeature : getFeatures(visibleFilter)) {
				featureMap.put(selectableFeature.getFeature().getName(), selectableFeature.getSelection() == Selection.SELECTED);
			}

			for (final SelectableFeature selectableFeature : featureList) {
				selectableFeature.setRecommended(Selection.UNDEFINED);
				selectableFeature.clearOpenClauses();
			}

			final Node[] clauses = rootNodeWithoutHidden.getCnf().getChildren();
			final HashMap<Object, Literal> literalMap = new HashMap<Object, Literal>();
			workMonitor.setRemainingWork(clauses.length);

			for (int i = 0; i < clauses.length; i++) {
				workMonitor.checkCancel();
				final Node clause = clauses[i];
				literalMap.clear();
				if (clause instanceof Literal) {
					final Literal literal = (Literal) clause;
					literalMap.put(literal.var, literal);
				} else {
					final Node[] orLiterals = clause.getChildren();
					for (int j = 0; j < orLiterals.length; j++) {
						final Literal literal = (Literal) orLiterals[j];
						literalMap.put(literal.var, literal);
					}
				}

				boolean satisfied = false;
				for (final Literal literal : literalMap.values()) {
					final Boolean selected = featureMap.get(literal.var);
					if ((selected != null) && (selected == literal.positive)) {
						satisfied = true;
						break;
					}
				}

				if (!satisfied) {
					int c = 0;
					boolean newLiterals = false;
					for (final SelectableFeature selectableFeature : featureList) {
						if (literalMap.containsKey(selectableFeature.getFeature().getName()) && !results[c]) {
							results[c] = true;

							switch (selectableFeature.getManual()) {
							case SELECTED:
								selectableFeature.setRecommended(Selection.UNSELECTED);
								selectableFeature.addOpenClause(openClauses.size(), clauses[i]);
								break;
							case UNSELECTED:
							case UNDEFINED:
								selectableFeature.setRecommended(Selection.SELECTED);
								selectableFeature.addOpenClause(openClauses.size(), clauses[i]);
							}
							newLiterals = true;
						}
						c++;
					}
					if (newLiterals) {
						openClauses.add(clause);
					}
				}
				workMonitor.worked();
			}
			return openClauses;
		}
	}

	public class GetSolutionsMethod implements LongRunningMethod<List<List<String>>> {

		private final int max;

		public GetSolutionsMethod(int max) {
			this.max = max;
		}

		@Override
		public List<List<String>> execute(IMonitor monitor) throws TimeoutException {
			if (rootNode == null) {
				return null;
			}

			final List<Literal> definedFeatures = new ArrayList<>();
			for (final SelectableFeature feature : getFeatures(selectedFilter)) {
				definedFeatures.add(getLiteral(feature));
			}

			final GetSolutionAnalysis analysis = new GetSolutionAnalysis(rootNode, max, true);
			analysis.setAssumptions(rootNode.convertToInt(definedFeatures));

			final List<int[]> solutions = LongRunningWrapper.runMethod(analysis);
			final List<List<String>> solutionList = new ArrayList<>(solutions.size());
			for (final int[] solution : solutions) {
				solutionList.add(rootNode.convertToString(solution, true, false));
			}
			return solutionList;
		}
	}

	/**
	 * Creates solutions to cover the given features.
	 *
	 * @param features The features that should be covered.
	 * @param selection true is the features should be selected, false otherwise.
	 */
	public class CoverFeaturesMethod implements LongRunningMethod<List<List<String>>> {

		private final Collection<String> features;
		private final boolean selection;

		public CoverFeaturesMethod(Collection<String> features, boolean selection) {
			this.features = features;
			this.selection = selection;
		}

		@Override
		public List<List<String>> execute(IMonitor monitor) throws TimeoutException {
			if (rootNode == null) {
				return Collections.emptyList();
			}

			final List<Literal> definedFeatures = new ArrayList<>();
			for (final SelectableFeature feature : getFeatures(selectedFilter)) {
				definedFeatures.add(getLiteral(feature));
			}

			final int[] literals = new int[features.size()];
			int index = 0;
			for (final String feature : features) {
				literals[index++] = (selection ? rootNode.getVariable(feature) : -rootNode.getVariable(feature));
			}

			final CoverAnalysis analysis = new CoverAnalysis(rootNode, literals);
			analysis.setAssumptions(rootNode.convertToInt(definedFeatures));

			final List<int[]> solutions = LongRunningWrapper.runMethod(analysis);
			if (solutions == null) {
				return Collections.emptyList();
			}
			final List<List<String>> solutionList = new ArrayList<>(solutions.size());
			for (final int[] solution : solutions) {
				solutionList.add(rootNode.convertToString(solution, true, false));
			}
			return solutionList;
		}
	}

	public class LeadToValidConfiguration implements LongRunningMethod<Void> {

		private static final int DEFAULT_MODE = -1;

		private final List<SelectableFeature> featureList;
		@SuppressWarnings("unused")
		private final int mode;

		public LeadToValidConfiguration(List<SelectableFeature> featureList) {
			this(featureList, DEFAULT_MODE);
		}

		public LeadToValidConfiguration(List<SelectableFeature> featureList, int mode) {
			this.featureList = featureList;
			this.mode = mode;
		}

		@Override
		public Void execute(IMonitor monitor) throws Exception {
			leadToValidConfig2(featureList, monitor);
			return null;
		}

		private void leadToValidConfig2(List<SelectableFeature> featureList, IMonitor workMonitor) {
			final boolean[] results = new boolean[featureList.size()];
			if (rootNode == null) {
				return;
			}
			final Map<String, Boolean> featureMap = new HashMap<String, Boolean>(configuration.features.size() << 1);

			for (final SelectableFeature selectableFeature : getFeatures(visibleFilter)) {
				featureMap.put(selectableFeature.getFeature().getName(), selectableFeature.getSelection() == Selection.SELECTED);
			}
			for (final SelectableFeature selectableFeature : featureList) {
				selectableFeature.setRecommended(Selection.UNDEFINED);
				selectableFeature.clearOpenClauses();
			}

			workMonitor.checkCancel();

			final Node[] clauses = rootNodeWithoutHidden.getCnf().getChildren();
			final HashMap<Object, Literal> literalMap = new HashMap<Object, Literal>();
			workMonitor.setRemainingWork(clauses.length);

			for (int i = 0; i < clauses.length; i++) {
				workMonitor.checkCancel();
				final Node clause = clauses[i];
				literalMap.clear();
				if (clause instanceof Literal) {
					final Literal literal = (Literal) clause;
					literalMap.put(literal.var, literal);
				} else {
					final Node[] orLiterals = clause.getChildren();
					for (int j = 0; j < orLiterals.length; j++) {
						final Literal literal = (Literal) orLiterals[j];
						literalMap.put(literal.var, literal);
					}
				}

				boolean satisfied = false;
				for (final Literal literal : literalMap.values()) {
					final Boolean selected = featureMap.get(literal.var);
					if ((selected != null) && (selected == literal.positive)) {
						satisfied = true;
						break;
					}
				}
				if (!satisfied) {
					int c = 0;
					for (final SelectableFeature selectableFeature : featureList) {
						if (literalMap.containsKey(selectableFeature.getFeature().getName()) && !results[c]) {
							results[c] = true;

							switch (selectableFeature.getManual()) {
							case SELECTED:
								selectableFeature.setRecommended(Selection.UNSELECTED);
								selectableFeature.addOpenClause(i, clause);
								break;
							case UNSELECTED:
							case UNDEFINED:
								selectableFeature.setRecommended(Selection.SELECTED);
								selectableFeature.addOpenClause(i, clause);
							}
						}
						workMonitor.invoke(selectableFeature);
						c++;
					}
				}
				workMonitor.worked();
			}
		}
	}

	public class LoadMethod implements LongRunningMethod<Void> {

		@Override
		public Void execute(IMonitor monitor) {
			if (rootNode != null) {
				return null;
			}
			final IFeatureModel featureModel = configuration.getFeatureModel();

			final AdvancedNodeCreator nodeCreator1, nodeCreator2;
			final IFilter<IFeature> filter1, filter2;
			if (configuration.ignoreAbstractFeatures) {
				filter1 = new HiddenFeatureFilter();
				filter2 = null;
				nodeCreator1 = new AdvancedNodeCreator(featureModel, filter1);
				nodeCreator2 = new AdvancedNodeCreator(featureModel);
			} else {
				filter1 = new OrFilter<>(Arrays.asList(new HiddenFeatureFilter(), new AbstractFeatureFilter()));
				filter2 = new AbstractFeatureFilter();
				nodeCreator1 = new AdvancedNodeCreator(featureModel, filter1);
				nodeCreator2 = new AdvancedNodeCreator(featureModel, filter2);
			}
			nodeCreator1.setCnfType(AdvancedNodeCreator.CNFType.Regular);
			nodeCreator2.setCnfType(AdvancedNodeCreator.CNFType.Regular);
			nodeCreator1.setIncludeBooleanValues(false);
			nodeCreator2.setIncludeBooleanValues(false);

			final IRunner<Node> buildThread1 = LongRunningWrapper.getThread(nodeCreator1);
			final IRunner<Node> buildThread2 = LongRunningWrapper.getThread(nodeCreator2);

			buildThread1.schedule();
			buildThread2.schedule();

			try {
				buildThread2.join();
				buildThread1.join();
			} catch (final InterruptedException e) {
				throw new MethodCancelException();
			}

			final Iterable<IFeature> features = featureModel.getFeatures();
			rootNodeWithoutHidden =
				new SatInstance(buildThread1.getResults(), Functional.mapToList(features, new InverseFilter<>(filter1), FeatureUtils.GET_FEATURE_NAME));
			rootNode = new SatInstance(buildThread2.getResults(),
					Functional.mapToList(features, filter2 == null ? null : new InverseFilter<>(filter2), FeatureUtils.GET_FEATURE_NAME));
			return null;
		}

	}

	public class UpdateMethod implements LongRunningMethod<Void> {

		private final boolean redundantManual;
		private final List<SelectableFeature> featureOrder;

		public UpdateMethod(boolean redundantManual) {
			this(redundantManual, null);
		}

		public UpdateMethod(boolean redundantManual, List<SelectableFeature> featureOrder) {
			this.redundantManual = redundantManual;
			this.featureOrder = featureOrder != null ? featureOrder : Collections.<SelectableFeature> emptyList();
		}

		@Override
		public Void execute(IMonitor workMonitor) {
			if (rootNode == null) {
				return null;
			}
			configuration.resetAutomaticValues();

			final ArrayList<Literal> manualLiterals = new ArrayList<>();
			for (final SelectableFeature feature : featureOrder) {
				if ((feature.getManual() != Selection.UNDEFINED) && (configuration.ignoreAbstractFeatures || FeatureUtils.isConcrete(feature.getFeature()))) {
					manualLiterals.add(getLiteral(feature));
				}
			}
			final HashSet<Literal> manualLiteralSet = new HashSet<>(manualLiterals);
			for (final SelectableFeature feature : getFeatures(manuallySelectedFilter)) {
				final Literal l = getLiteral(feature);
				if (manualLiteralSet.add(l)) {
					manualLiterals.add(l);
				}
			}

			workMonitor.setRemainingWork(manualLiterals.size() + 1);
			Collections.reverse(manualLiterals);

			final ConditionallyCoreDeadAnalysis analysis = new ConditionallyCoreDeadAnalysis(rootNode);
			final int[] intLiterals = rootNode.convertToInt(manualLiterals);
			analysis.setAssumptions(intLiterals);
			final int[] impliedFeatures = LongRunningWrapper.runMethod(analysis, workMonitor.subTask(1));

			// if there is a contradiction within the configuration
			if (impliedFeatures == null) {
				return null;
			}

			for (final int i : impliedFeatures) {
				final SelectableFeature feature = configuration.getSelectablefeature((String) rootNode.getVariableObject(i));
				configuration.setAutomatic(feature, i > 0 ? Selection.SELECTED : Selection.UNSELECTED);
				workMonitor.invoke(feature);
				manualLiteralSet.add(new Literal(feature.getFeature().getName(), feature.getManual() == Selection.SELECTED));
			}
			// only for update of configuration editor
			for (final SelectableFeature feature : configuration.features) {
				if (!manualLiteralSet.contains(new Literal(feature.getFeature().getName(), feature.getManual() == Selection.SELECTED))) {
					workMonitor.invoke(feature);
				}
			}

			if (redundantManual) {
				computeRedundantManual(workMonitor, intLiterals);
			}
			return null;
		}

		private void computeRedundantManual(IMonitor workMonitor, final int[] intLiterals) {
			final BasicSolver solver;
			try {
				solver = new BasicSolver(rootNode);
			} catch (final ContradictionException e) {
				Logger.logError(e);
				return;
			}

			for (final int feature : intLiterals) {
				solver.assignmentPush(feature);
			}

			int literalCount = intLiterals.length;
			final IVecInt assignment = solver.getAssignment();
			for (int i = 0; i < assignment.size(); i++) {
				final int oLiteral = intLiterals[i];
				final SelectableFeature feature = configuration.getSelectablefeature((String) rootNode.getVariableObject(oLiteral));
				assignment.set(i, -oLiteral);
				final SatResult satResult = solver.isSatisfiable();
				switch (satResult) {
				case FALSE:
					configuration.setAutomatic(feature, oLiteral > 0 ? Selection.SELECTED : Selection.UNSELECTED);
					workMonitor.invoke(feature);
					intLiterals[i] = intLiterals[--literalCount];
					assignment.delete(i--);
					break;
				case TIMEOUT:
				case TRUE:
					assignment.set(i, oLiteral);
					workMonitor.invoke(feature);
					break;
				default:
					throw new AssertionError(satResult);
				}
				workMonitor.worked();
			}
		}

	}

	private final Configuration configuration;

	private SatInstance rootNode = null, rootNodeWithoutHidden = null;

	/**
	 * This method creates a clone of the given {@link ConfigurationPropagator}
	 *
	 * @param configuration The configuration to clone
	 */
	ConfigurationPropagator(Configuration configuration) {
		this.configuration = configuration;
	}

	ConfigurationPropagator(ConfigurationPropagator propagator) {
		this(propagator, propagator.configuration);
	}

	ConfigurationPropagator(ConfigurationPropagator propagator, Configuration configuration) {
		this.configuration = configuration;
		if (propagator.isLoaded()) {
			rootNode = propagator.rootNode;
			rootNodeWithoutHidden = propagator.rootNodeWithoutHidden;
		}
	}

	@Override
	public IsValidMethod canBeValid() {
		return new IsValidMethod(false, true);
	}

	/**
	 * Creates solutions to cover the given features.
	 *
	 * @param features The features that should be covered.
	 * @param selection true is the features should be selected, false otherwise.
	 */
	public CoverFeaturesMethod coverFeatures(final Collection<String> features, final boolean selection) throws TimeoutException {
		return new CoverFeaturesMethod(features, selection);
	}

	@Override
	public FindClause findOpenClauses(List<SelectableFeature> featureList) {
		return new FindClause(featureList);
	}

	@Override
	public Resolve resolve() {
		return new Resolve();
	}

	@Override
	public GetSolutionsMethod getSolutions(int max) throws TimeoutException {
		return new GetSolutionsMethod(max);
	}

	@Override
	public boolean isLoaded() {
		return rootNode != null;
	}

	@Override
	public IsValidMethod isValid() {
		return new IsValidMethod(true, true);
	}

	/**
	 * Ignores hidden features. Use this, when propgate is disabled (hidden features are not updated).
	 */
	@Override
	public IsValidMethod isValidNoHidden() {
		return new IsValidMethod(true, false);
	}

	@Override
	public LeadToValidConfiguration leadToValidConfiguration(List<SelectableFeature> featureList) {
		return new LeadToValidConfiguration(featureList);
	}

	@Override
	public LeadToValidConfiguration leadToValidConfiguration(List<SelectableFeature> featureList, int mode) {
		return new LeadToValidConfiguration(featureList, mode);
	}

	@Override
	public LoadMethod load() {
		return new LoadMethod();
	}

	/**
	 * Counts the number of possible solutions.
	 *
	 * @return a positive value equal to the number of solutions (if the method terminated in time)</br> or a negative value (if a timeout occurred) that
	 *         indicates that there are more solutions than the absolute value
	 */
	@Override
	public CountSolutionsMethod number(long timeout, boolean includeHiddenFeatures) {
		return new CountSolutionsMethod(timeout, includeHiddenFeatures);
	}

	@Override
	public UpdateMethod update(boolean redundantManual, List<SelectableFeature> featureOrder) {
		return new UpdateMethod(redundantManual, featureOrder);
	}

	@Override
	public UpdateMethod update(boolean redundantManual) {
		return update(redundantManual, null);
	}

	@Override
	public UpdateMethod update() {
		return update(false, null);
	}

	protected ConfigurationPropagator clone(Configuration configuration) {
		return new ConfigurationPropagator(this, configuration);
	}

	@SafeVarargs
	private final Iterable<SelectableFeature> getFeatures(IFilter<SelectableFeature>... filter) {
		final Iterable<SelectableFeature> source = configuration.ignoreAbstractFeatures ? Functional.filter(configuration.features, invalidFeatureFilter)
			: Functional.filter(configuration.features, invalidFeatureFilter, concreteFilter);
		return filter.length > 0 ? Functional.filter(source, filter) : source;
	}

}
