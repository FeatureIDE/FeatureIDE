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

import static de.ovgu.featureide.fm.core.functional.Functional.map;
import static de.ovgu.featureide.fm.core.localization.StringTable.ANALYZE;
import static de.ovgu.featureide.fm.core.localization.StringTable.CALCULATE_INDETRMINATE_HIDDEN_FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.CALCULATE_INDETRMINATE_HIDDEN_FEATURES_FOR;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;
import org.prop4j.SatSolver;
import org.prop4j.analyses.FeatureModelAnalysis;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.fm.DeadFeatureExplanation;
import de.ovgu.featureide.fm.core.explanations.fm.DeadFeatureExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.fm.FalseOptionalFeatureExplanation;
import de.ovgu.featureide.fm.core.explanations.fm.FalseOptionalFeatureExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelExplanationCreatorFactory;
import de.ovgu.featureide.fm.core.explanations.fm.RedundantConstraintExplanation;
import de.ovgu.featureide.fm.core.explanations.fm.RedundantConstraintExplanationCreator;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.functional.Functional.IFunction;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.NullMonitor;

/**
 * A collection of methods for working with {@link IFeatureModel} will replace the corresponding methods in {@link IFeatureModel}
 *
 * @author Soenke Holthusen
 * @author Florian Proksch
 * @author Stefan Krueger
 * @author Marcus Pinnecke (Feature Interface)
 */
public class FeatureModelAnalyzer implements IEventListener {

	/**
	 * Remembers explanations for dead features.
	 */
	private final Map<IFeature, DeadFeatureExplanation> deadFeatureExplanations = new HashMap<>();
	/**
	 * Remembers explanations for false-optional features.
	 */
	private final Map<IFeature, FalseOptionalFeatureExplanation> falseOptionalFeatureExplanations = new HashMap<>();
	/**
	 * Remembers explanations for redundant constraints.
	 */
	private final Map<IConstraint, RedundantConstraintExplanation> redundantConstraintExplanations = new HashMap<>();
	/**
	 * Used for creating explanation creators.
	 */
	private final FeatureModelExplanationCreatorFactory explanationCreatorFactory = FeatureModelExplanationCreatorFactory.getDefault();
	/**
	 * Creates explanations for dead features. Stored for performance so the underlying CNF is not recreated for every explanation.
	 */
	private final DeadFeatureExplanationCreator deadFeatureExplanationCreator = explanationCreatorFactory.getDeadFeatureExplanationCreator();
	/**
	 * Creates explanations for false-optional features. Stored for performance so the underlying CNF is not recreated for every explanation.
	 */
	private final FalseOptionalFeatureExplanationCreator falseOptionalFeatureExplanationCreator =
		explanationCreatorFactory.getFalseOptionalFeatureExplanationCreator();
	/**
	 * Creates explanations for redundant constraints. Stored for performance so the underlying CNF is not recreated for every explanation.
	 */
	private final RedundantConstraintExplanationCreator redundantConstraintExplanationCreator =
		explanationCreatorFactory.getRedundantConstraintExplanationCreator();

	public static enum Attribute {
		Mandatory, Optional, Alternative, Or, Abstract, Concrete, Hidden, Dead, FalseOptional, IndetHidden, UnsatisfiableConst, TautologyConst, VoidModelConst, RedundantConst
	}

	private static final String TRUE = NodeCreator.varTrue.toString();
	private static final String FALSE = NodeCreator.varFalse.toString();

	private List<IFeature> cachedDeadFeatures = Collections.emptyList();
	private List<IFeature> cachedCoreFeatures = Collections.emptyList();
	private List<IFeature> cachedFalseOptionalFeatures = Collections.emptyList();

	private Boolean cachedValidity = null;

	private final IFeatureModel fm;
	/**
	 * The feature model as a formula in conjunctive normal form. Created lazily. Resets when the feature model changes.
	 */
	private Node cnf;

	/**
	 * Defines whether features should be included into calculations. If features are not analyzed, then constraints a also NOT analyzed.
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
	 * A flag indicating that the calculation should be canceled.
	 */
	private boolean cancel = false;

	private IMonitor monitor = new NullMonitor();

	private FeatureDependencies dependencies;

	/**
	 * Returns the cached value. Calculated on the first call and on each call of updateFeatureModel().
	 *
	 * @return cached value
	 */
	public boolean valid() {
		if (cachedValidity == null) {
			try {
				cachedValidity = isValid();
			} catch (final TimeoutException e) {
				Logger.logError(e);
			}
		}
		return cachedValidity;
	}

	public FeatureModelAnalyzer(IFeatureModel fm) {
		this.fm = fm;
		fm.addListener(this);
		clearExplanations();
	}

	public FeatureModelAnalyzer(FeatureModelAnalyzer oldAnalyzer, IFeatureModel newFM) {
		fm = newFM;
		fm.addListener(this);
		clearExplanations();

		calculateConstraints = oldAnalyzer.calculateConstraints;
		calculateDeadConstraints = oldAnalyzer.calculateDeadConstraints;
		calculateFeatures = oldAnalyzer.calculateFeatures;
		calculateFOConstraints = oldAnalyzer.calculateFOConstraints;
		calculateRedundantConstraints = oldAnalyzer.calculateRedundantConstraints;
		calculateTautologyConstraints = oldAnalyzer.calculateTautologyConstraints;
		runCalculationAutomatically = oldAnalyzer.runCalculationAutomatically;
	}

	/**
	 * Returns the feature dependencies of the feature model. If the has model changed call {@link FeatureModelAnalyzer#setDependencies()} to calculate current
	 * dependencies.
	 *
	 * @return
	 */
	public FeatureDependencies getDependencies() {
		if (dependencies == null) {
			dependencies = new FeatureDependencies(fm);
		}
		return dependencies;
	}

	/**
	 * Calculates new dependencies.
	 *
	 * @return
	 */
	public void setDependencies() {
		dependencies = new FeatureDependencies(fm);
	}

	/**
	 * Returns the value calculated by the SatSolver
	 *
	 * @return value
	 * @throws TimeoutException after 1000ms
	 */
	public boolean isValid() throws TimeoutException {
		return new SatSolver(getCnf(), 1000, false).isSatisfiable();
	}

	/**
	 * <p> Returns whether the conjunction of A always implies the disjunction of B in the current feature model. </p>
	 *
	 * <p> In other words, the following satisfiability query is checked: <pre>TAUT(FM &rArr; ((&and;<sub>a&in;A</sub> a) &rArr; (&or;<sub>b&in;B</sub>
	 * b)))</pre> </p>
	 *
	 * <p> Note that this formula is always true if B is empty. </p>
	 *
	 * @param a set of features that form a conjunction
	 * @param b set of features that form a disjunction
	 * @return whether the conjunction of A always implies the disjunction of B in the current feature model
	 * @throws TimeoutException
	 */
	public boolean checkImplies(Collection<IFeature> a, Collection<IFeature> b) throws TimeoutException {
		if (b.isEmpty()) {
			return true;
		}

		/*
		 * TAUT(FM => (A => B)) = TAUT(-FM | -A | B) = -SAT(-(-FM | -A | B)) = -SAT(FM & A & -B) = -SAT(FM & A1 & ... & An & -(B1 | ... | Bm)) = -SAT(FM & A1 &
		 * ... & An & -B1 & ... & -Bm)
		 */
		final Node[] literals = new Node[a.size() + b.size()];
		int i = 0;
		for (final IFeature f : a) {
			literals[i++] = new Literal(NodeCreator.getVariable(f, fm));
		}
		for (final IFeature f : b) {
			literals[i++] = new Literal(NodeCreator.getVariable(f, fm), false);
		}
		return !new SatSolver(getCnf(), 1000).isSatisfiable(new And(literals));
	}

	public boolean checkIfFeatureCombinationNotPossible(IFeature a, Collection<IFeature> b) throws TimeoutException {
		if (b.isEmpty()) {
			return true;
		}

		/*
		 * -SAT(FM & A & B1) | ... | -SAT(FM & A & Bn)
		 */
		final SatSolver solver = new SatSolver(getCnf(), 1000);
		for (final IFeature f : b) {
			final Node featureCombination = new And(NodeCreator.getVariable(a, fm), NodeCreator.getVariable(f, fm));
			if (!solver.isSatisfiable(featureCombination)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * checks some condition against the feature model. use only if you know what you are doing!
	 *
	 * @return
	 * @throws TimeoutException
	 */
	public boolean checkCondition(Node condition) {
		try {
			return isImpliedTautology(condition);
		} catch (final TimeoutException e) {
			Logger.logError(e);
			return false;
		}
	}

	/**
	 * <p> Returns whether the given condition is always implied by the feature model. </p>
	 *
	 * <p> In other words, the following satisfiability query is checked: <pre>TAUT(FM &rArr; C)</pre> </p>
	 *
	 * @param condition implied condition
	 * @return whether the given condition is always implied by the feature model
	 * @throws TimeoutException
	 */
	private boolean isImpliedTautology(Node condition) throws TimeoutException {
		/*
		 * TAUT(FM => C) = TAUT(-FM | C) = -SAT(-(-FM | C)) = -SAT(FM & -C)
		 */
		return !new SatSolver(getCnf(), 1000).isSatisfiable(new Not(condition));
	}

	/**
	 * Checks whether the given featureSets are mutually exclusive in the given context and for the current feature model.
	 *
	 * In detail it is checked whether FM => (context => (at most one of the featureSets are present)) is a tautology.
	 *
	 * Here is an example for a truth table of AT_MOST_ONE_THE_FEATURESETS_ARE_PRESENT for three feature sets A, B and C:
	 *
	 * A B C result ------------------------ T T T F T T F F T F T F T F F T F T T F F T F T F F T T F F F T
	 *
	 * If you want to check XOR(featureSet_1, ..., featureSet_n) you can call areMutualExclusive() && !mayBeMissing().
	 *
	 * @param context context in which everything is checked
	 * @param featureSets list of feature sets that are checked to be mutually exclusive in the given context and for the current feature model
	 *
	 * @return true, if the feature sets are mutually exclusive || false, otherwise
	 * @throws TimeoutException
	 */
	@Deprecated
	public boolean areMutualExclusive(Collection<IFeature> context, Collection<Set<IFeature>> featureSets) throws TimeoutException {
		if ((featureSets == null) || (featureSets.size() < 2)) {
			return true;
		}

		final ArrayList<Node> conjunctions = new ArrayList<Node>(featureSets.size());
		for (final Collection<IFeature> features : featureSets) {
			if ((features != null) && !features.isEmpty()) {
				conjunctions.add(conjunct(features));
			} else {
				// If one feature set is empty (i.e. the code-fragment is always
				// present) than it cannot be
				// mutually exclusive to the other ones.
				return false;
			}
		}

		// We build the conjunctive normal form of the formula to check
		final Collection<Object> forOr = new LinkedList<Object>();
		final Collection<Object> allNot = new LinkedList<Object>();
		for (int i = 0; i < conjunctions.size(); ++i) {
			allNot.add(new Not(conjunctions.get(i).clone()));

			final Collection<Object> forAnd = new LinkedList<Object>();
			for (int j = 0; j < conjunctions.size(); ++j) {
				if (j == i) {
					forAnd.add(conjunctions.get(j).clone());
				} else {
					forAnd.add(new Not(conjunctions.get(j).clone()));
				}
			}
			forOr.add(new And(forAnd));
		}
		forOr.add(new And(allNot));

		Node condition = new Or(forOr);
		if ((context != null) && !context.isEmpty()) {
			condition = new Implies(conjunct(context), condition);
		}

		return isImpliedTautology(condition);
	}

	/**
	 * Checks whether there exists a set of features that is valid within the feature model and the given context, so that none of the given feature sets are
	 * present, i.e. evaluate to true.
	 *
	 * In detail it is checked whether there exists a set F of features so that eval(FM, F) AND eval(context, F) AND NOT(eval(featureSet_1, F)) AND ... AND
	 * NOT(eval(featureSet_n, F)) is true.
	 *
	 * If you want to check XOR(featureSet_1, ..., featureSet_n) you can call areMutualExclusive() && !mayBeMissing().
	 *
	 * @param context context in which everything is checked
	 * @param featureSets list of feature sets
	 *
	 * @return true, if there exists such a set of features, i.e. if the code-fragment may be missing || false, otherwise
	 * @throws TimeoutException
	 */
	@Deprecated
	public boolean mayBeMissing(Collection<IFeature> context, Collection<Set<IFeature>> featureSets) throws TimeoutException {
		if ((featureSets == null) || featureSets.isEmpty()) {
			return false;
		}

		final Collection<Object> forAnd = new LinkedList<Object>();

		for (final Collection<IFeature> features : featureSets) {
			if ((features != null) && !features.isEmpty()) {
				forAnd.add(new Not(conjunct(features)));
			} else {
				return false;
			}
		}

		Node condition = new And(forAnd);
		if ((context != null) && !context.isEmpty()) {
			condition = new And(conjunct(context), condition);
		}

		return new SatSolver(getCnf(), 1000).isSatisfiable(condition);
	}

	/**
	 * Checks whether there exists a set of features that is valid within the feature model, so that all given features are present.
	 *
	 * In detail it is checked whether there exists a set F of features so that eval(FM, F) AND eval(feature_1, F) AND eval(feature_n, F) is true.
	 *
	 * @param features
	 *
	 * @return true if there exists such a set of features || false, otherwise
	 * @throws TimeoutException
	 */
	@Deprecated
	public boolean exists(Collection<IFeature> features) throws TimeoutException {
		if ((features == null) || features.isEmpty()) {
			return true;
		}
		return new SatSolver(getCnf(), 1000).isSatisfiable(conjunct(features));
	}

	@Deprecated
	public Node conjunct(final Collection<IFeature> b) {
		return new And(new And(Functional.toList(map(b, new IFunction<IFeature, Literal>() {

			@Override
			public Literal invoke(IFeature t) {
				return new Literal(NodeCreator.getVariable(t, fm));
			}

		}))), fm);
	}

	@Deprecated
	public Node disjunct(Collection<IFeature> b) {
		final Iterator<IFeature> iterator = b.iterator();
		Node result = new Literal(NodeCreator.getVariable(iterator.next(), fm));
		while (iterator.hasNext()) {
			result = new Or(result, new Literal(NodeCreator.getVariable(iterator.next(), fm)));
		}

		return result;
	}

	/**
	 * Returns the list of features that occur in all variants, where one of the given features is selected. If the given list of features is empty, this method
	 * will calculate the features that are present in all variants specified by the feature model.
	 *
	 * @param timeout in milliseconds
	 * @param selectedFeatures a list of feature names for which
	 * @return a list of features that is common to all variants
	 */
	@Deprecated
	public Collection<String> commonFeatures(long timeout, Object... selectedFeatures) {
		Node formula = getCnf();
		if (selectedFeatures.length > 0) {
			formula = new And(formula, new Or(selectedFeatures));
		}
		final Collection<String> common = new ArrayList<>();
		final SatSolver solver = new SatSolver(formula, timeout);
		for (final Literal literal : solver.knownValues(SatSolver.ValueType.TRUE)) {
			common.add(literal.var.toString());
		}
		return common;
	}

	/**
	 * Adds the propNode to the solver to calculate dead features.
	 */
	public List<IFeature> getDeadFeatures(SatSolver solver, Node propNode) {
		solver.addClauses(propNode.clone().toCNF());
		final ArrayList<IFeature> deadFeatures = new ArrayList<>();
		deadFeatures.clear();

		for (final Literal e : solver.knownValues(SatSolver.ValueType.FALSE)) {
			final String var = e.var.toString();
			if (!FALSE.equals(var) && !TRUE.equals(var)) {
				final IFeature feature = fm.getFeature(var);
				if (feature != null) {
					deadFeatures.add(feature);
				}
			}
		}

		cachedDeadFeatures = deadFeatures;
		return getCachedDeadFeatures();
	}

	public List<IFeature> getCoreFeatures() {
		return getCoreFeatures(1000);
	}

	public List<IFeature> getDeadFeatures() {
		return getDeadFeatures(1000);
	}

	public List<List<IFeature>> analyzeFeatures() {
		return analyzeFeatures(1000);
	}

	public List<IFeature> getCoreFeatures(long timeout, Object... selectedFeatures) {
		return analyzeFeatures(timeout, SatSolver.ValueType.TRUE, selectedFeatures).get(0);
	}

	public List<IFeature> getDeadFeatures(long timeout, Object... selectedFeatures) {
		return analyzeFeatures(timeout, SatSolver.ValueType.FALSE, selectedFeatures).get(1);
	}

	public List<List<IFeature>> analyzeFeatures(long timeout, Object... selectedFeatures) {
		return analyzeFeatures(timeout, SatSolver.ValueType.ALL, selectedFeatures);
	}

	private List<List<IFeature>> analyzeFeatures(long timeout, SatSolver.ValueType vt, Object... selectedFeatures) {
		final ArrayList<IFeature> coreFeatures = new ArrayList<>();
		final ArrayList<IFeature> deadFeatures = new ArrayList<>();

		Node formula = getCnf();
		if (selectedFeatures.length > 0) {
			final Node[] extendedChildren = Arrays.copyOf(formula.getChildren(), formula.getChildren().length + 1);
			extendedChildren[formula.getChildren().length] = new Or(selectedFeatures);
			formula = new And(extendedChildren);
		}
		final SatSolver solver = new SatSolver(formula, timeout, false);

		for (final Literal literal : solver.knownValues(vt)) {
			final String var = literal.var.toString();
			if (!FALSE.equals(var) && !TRUE.equals(var)) {
				final IFeature feature = fm.getFeature(var);
				if (feature != null) {
					if (literal.positive) {
						coreFeatures.add(feature);
					} else {
						deadFeatures.add(feature);
					}
				}
			}
		}

		cachedCoreFeatures = coreFeatures;
		cachedDeadFeatures = deadFeatures;

		final ArrayList<List<IFeature>> result = new ArrayList<>(2);
		result.add(getCachedCoreFeatures());
		result.add(getCachedDeadFeatures());

		return result;
	}

	public List<List<IFeature>> getAtomicSets() {
		final ArrayList<List<IFeature>> result = new ArrayList<>();

		final SatSolver solver = new SatSolver(getCnf(), 1000, false);

		for (final List<Literal> literalList : solver.atomicSets()) {
			final List<IFeature> setList = new ArrayList<>();
			result.add(setList);
			for (final Literal literal : literalList) {
				final String var = literal.var.toString();
				if (!FALSE.equals(var) && !TRUE.equals(var)) {
					final IFeature feature = fm.getFeature(var);
					if (feature != null) {
						setList.add(feature);
					}
				}
			}

		}
		return result;
	}

	/**
	 * @param monitor
	 * @return Hashmap: key entry is Feature/Constraint, value usually indicating the kind of attribute
	 */
	/*
	 * check all changes of this method and called methods with the related tests and benchmarks, see fm.core-test plug-in think about performance (no
	 * unnecessary or redundant calculations) Hashing might be fast for locating features, but creating a HashSet is costly So LinkedLists are much faster
	 * because the number of feature in the set is usually small (e.g. dead features)
	 */
	public HashMap<Object, Object> analyzeFeatureModel(IMonitor monitor) {
		this.monitor = monitor == null ? new NullMonitor() : monitor;
		final FeatureModelAnalysis analysis = new FeatureModelAnalysis(fm);
		analysis.setCalculateFeatures(calculateFeatures);
		analysis.setCalculateConstraints(calculateConstraints);
		analysis.setCalculateRedundantConstraints(calculateRedundantConstraints);
		analysis.setCalculateTautologyConstraints(calculateTautologyConstraints);
		analysis.setCalculateDeadConstraints(calculateDeadConstraints);
		analysis.setCalculateFOConstraints(calculateFOConstraints);
		final HashMap<Object, Object> newAttributes = LongRunningWrapper.runMethod(analysis, this.monitor);
		cachedValidity = analysis.isValid();
		cachedCoreFeatures = analysis.getCoreFeatures();
		cachedDeadFeatures = analysis.getDeadFeatures();
		cachedFalseOptionalFeatures = analysis.getFalseOptionalFeatures();
		clearExplanations();
		return newAttributes;
	}

	private void beginTask(int totalWork) {
		monitor.setTaskName(ANALYZE);
		monitor.setRemainingWork(totalWork);
	}

	public void updateConstraints() {
		final FeatureModelAnalysis analysis = new FeatureModelAnalysis(fm);
		analysis.setCalculateFeatures(false);
		analysis.setCalculateConstraints(true);
		analysis.setCalculateRedundantConstraints(calculateRedundantConstraints);
		analysis.setCalculateTautologyConstraints(calculateTautologyConstraints);
		analysis.setCalculateDeadConstraints(calculateDeadConstraints);
		analysis.setCalculateFOConstraints(calculateFOConstraints);
		analysis.updateConstraints();
		cachedValidity = analysis.isValid();
	}

	private boolean canceled() {
		monitor.checkCancel();
		return cancel;
	}

	private void worked(int workDone) {
		monitor.step();
	}

	public void updateFeatures() {
		final FeatureModelAnalysis analysis = new FeatureModelAnalysis(fm);
		analysis.setCalculateFeatures(true);
		analysis.setCalculateConstraints(false);
		analysis.updateFeatures();
		cachedValidity = analysis.isValid();
		cachedCoreFeatures = analysis.getCoreFeatures();
		cachedDeadFeatures = analysis.getDeadFeatures();
		cachedFalseOptionalFeatures = analysis.getFalseOptionalFeatures();
	}

	/**
	 * Calculations for indeterminate hidden features
	 *
	 * @param changedAttributes
	 */
	public void calculateHidden(Map<Object, Object> changedAttributes) {
		if (!fm.getStructure().hasHidden()) {
			return;
		}
		monitor.setTaskName(CALCULATE_INDETRMINATE_HIDDEN_FEATURES);
		/**
		 * First every relevant constraint of every hidden feature is checked if its form equals HIDDEN_FEATURE <=> A where A is an expression containing only
		 * non hidden features If there is a constraint of that kind for a hidden feature it is added to a list.
		 */
		final IFeatureModelFactory factory = FMFactoryManager.getFactory(fm);
		final Collection<IFeature> list = new LinkedList<IFeature>();
		final Collection<IFeature> hiddenFeatures = getHiddenFeatures();
		for (final IFeature feature : hiddenFeatures) {
			for (final IConstraint constraint : feature.getStructure().getRelevantConstraints()) {
				final Node node = constraint.getNode();
				if (node instanceof Equals) {
					final Node[] children = node.getChildren();
					final Node leftChild = children[0];
					final Node rightChild = children[1];
					if ((leftChild instanceof Literal) && ((Literal) leftChild).var.equals(feature.getName())) {
						final IConstraint rightConstraint = factory.createConstraint(fm, rightChild);
						rightConstraint.setContainedFeatures();
						if (!rightConstraint.hasHiddenFeatures()) {
							list.add(feature);
							break;
						}
					}
					if ((rightChild instanceof Literal) && ((Literal) rightChild).var.equals(feature.getName())) {
						final IConstraint leftConstraint = factory.createConstraint(fm, leftChild);
						leftConstraint.setContainedFeatures();
						if (!leftConstraint.hasHiddenFeatures()) {
							list.add(feature);
							break;
						}
					}
				}
			}
		}

		/**
		 * Additionally each Node is checked if the atomic set containing it, consists of indeterminate hidden nodes only. If this is the case it's also
		 * indeterminate. A node is therefore not marked indeterminate if it either - has a non-hidden Node in its atomic set defining its state or - if a Node
		 * of its atomic set is determined by a constraint of the above form.
		 */
		final FeatureDependencies featureDependencies = new FeatureDependencies(fm, false);
		beginTask(fm.getConstraintCount() + hiddenFeatures.size());
		for (final IFeature feature : hiddenFeatures) {
			if (canceled()) {
				return;
			}
			monitor.setTaskName(CALCULATE_INDETRMINATE_HIDDEN_FEATURES_FOR + feature.getName());
			if (!list.contains(feature)) {
				final Collection<IFeature> set = featureDependencies.getImpliedFeatures(feature);
				boolean noHidden = false;
				for (final IFeature f : set) {
					if ((!f.getStructure().isHidden() && !f.getStructure().hasHiddenParent()) || list.contains(f)) {
						if (featureDependencies.isAlways(f, feature)) {
							noHidden = true;
							break;
						}
					}
				}

				if (!noHidden) {
					changedAttributes.put(feature, FeatureStatus.INDETERMINATE_HIDDEN);
					feature.getProperty().setFeatureStatus(FeatureStatus.INDETERMINATE_HIDDEN, false);
				}

				worked(1);
			}
		}
	}

	/**
	 * Gets all hidden features their children
	 *
	 * @return
	 */
	public Collection<IFeature> getHiddenFeatures() {
		final Collection<IFeature> hiddenFeatures = new LinkedList<IFeature>();
		for (final IFeature f : fm.getFeatures()) {
			if (f.getStructure().isHidden() || f.getStructure().hasHiddenParent()) {
				hiddenFeatures.add(f);
			}
		}
		return hiddenFeatures;
	}

	public List<IFeature> getFalseOptionalFeatures() {
		return getFalseOptionalFeatures(fm.getFeatures());
	}

	public List<IFeature> getFalseOptionalFeatures(Iterable<IFeature> fmFalseOptionals) {
		final List<IFeature> falseOptionalFeatures = new ArrayList<>();

		final SatSolver solver = new SatSolver(getCnf(), 1000);
		for (final IFeature feature : fmFalseOptionals) {
			final IFeatureStructure structure = feature.getStructure();
			if (!FeatureUtils.getRoot(fm).getName().equals(feature.getName())) { // this might be indeed the case within the analysis for subtree dependencies
				final IFeature parent = FeatureUtils.getParent(feature);
				if (!structure.isMandatory() && (parent != null) && solver.isImplied(new Literal(parent.getName(), false), new Literal(feature.getName()))) {
					falseOptionalFeatures.add(feature);
				}
			}
		}
		return falseOptionalFeatures;
	}

	public int countConcreteFeatures() {
		int number = 0;
		for (final IFeature feature : fm.getFeatures()) {
			if (feature.getStructure().isConcrete()) {
				number++;
			}
		}
		return number;
	}

	public int countHiddenFeatures() {
		int number = 0;
		for (final IFeature feature : fm.getFeatures()) {
			final IFeatureStructure structure = feature.getStructure();
			if (structure.isHidden() || structure.hasHiddenParent()) {
				number++;
			}
		}
		return number;
	}

	public int countTerminalFeatures() {
		int number = 0;
		for (final IFeature feature : fm.getFeatures()) {
			if (!feature.getStructure().hasChildren()) {
				number++;
			}
		}
		return number;
	}

	/**
	 * Sets the cancel status of analysis.<br> <code>true</code> if analysis should be stopped.
	 */
	public void cancel(boolean value) {
		cancel = value;
	}

	public List<IFeature> getCachedDeadFeatures() {
		return Collections.unmodifiableList(cachedDeadFeatures);
	}

	public List<IFeature> getCachedCoreFeatures() {
		return Collections.unmodifiableList(cachedCoreFeatures);
	}

	public Collection<IFeature> getCachedFalseOptionalFeatures() {
		return Collections.unmodifiableList(cachedFalseOptionalFeatures);
	}

	/**
	 * Listens to feature model changes. Resets its formula if necessary.
	 */
	@Override
	public void propertyChange(FeatureIDEEvent event) {
		switch (event.getEventType()) {
		case ALL_FEATURES_CHANGED_NAME_TYPE: // Required because feature names are used as variable names.
		case CHILDREN_CHANGED:
		case CONSTRAINT_ADD:
		case CONSTRAINT_DELETE:
		case CONSTRAINT_MODIFY:
		case FEATURE_ADD:
		case FEATURE_ADD_ABOVE:
		case FEATURE_DELETE:
		case FEATURE_MODIFY: // TODO If a formula reset is required for this event type, remove this comment. Otherwise, remove this case.
		case FEATURE_NAME_CHANGED: // Required because feature names are used as variable names.
		case GROUP_TYPE_CHANGED:
		case HIDDEN_CHANGED: // TODO If a formula reset is required for this event type, remove this comment. Otherwise, remove this case.
		case MANDATORY_CHANGED:
		case MODEL_DATA_CHANGED:
		case MODEL_DATA_LOADED:
		case MODEL_DATA_OVERRIDDEN:
		case PARENT_CHANGED:
		case STRUCTURE_CHANGED:
			cnf = null;
			break;
		default:
			break;
		}
	}

	/**
	 * <p> Returns the feature model as a formula in conjunctive normal form. Creates it first if necessary. </p>
	 *
	 * <p> As this is a cached mutable object, care must be taken not to modify the returned object or any of its children. If changes are necessary, the
	 * returned object must be cloned first. </p>
	 *
	 * @return the feature model as a formula in conjunctive normal form; not null
	 * @see {@link #getNode()} if the formula does not have to be in conjunctive normal form
	 */
	public Node getCnf() {
		if (cnf == null) {
			cnf = createCnf();
		}
		return cnf;
	}

	/**
	 * Creates the feature model as a formula in conjunctive normal form.
	 *
	 * @return the feature model as a formula in conjunctive normal form; not null
	 */
	private Node createCnf() {
		return AdvancedNodeCreator.createRegularCNF(fm);
	}

	/**
	 * Returns an explanation why the given feature model element is defect.
	 *
	 * @param modelElement potentially defect feature model element; not null
	 * @return an explanation; null if it cannot be explained
	 */
	public Explanation<?> getExplanation(IFeatureModelElement modelElement) {
		return getExplanation(fm, modelElement);
	}

	/**
	 * Returns an explanation why the given feature model element is defect.
	 *
	 * @param fm feature model containing the feature model element; not null
	 * @param modelElement potentially defect feature model element; not null
	 * @return an explanation; null if it cannot be explained
	 */
	public Explanation<?> getExplanation(IFeatureModel fm, IFeatureModelElement modelElement) {
		Explanation<?> explanation = null;
		if (modelElement instanceof IFeature) {
			final IFeature feature = (IFeature) modelElement;
			switch (feature.getProperty().getFeatureStatus()) {
			case DEAD:
				explanation = getDeadFeatureExplanation(fm, feature);
				break;
			case FALSE_OPTIONAL:
				explanation = getFalseOptionalFeatureExplanation(fm, feature);
				break;
			default:
				break;
			}
		} else if (modelElement instanceof IConstraint) {
			final IConstraint constraint = (IConstraint) modelElement;
			switch (constraint.getConstraintAttribute()) {
			case REDUNDANT:
			case IMPLICIT:
				explanation = getRedundantConstraintExplanation(fm, constraint);
				break;
			default:
				break;
			}
		}
		return explanation;
	}

	/**
	 * Returns an explanation why the feature model is void. That is the same explanation for why its root feature is dead.
	 *
	 * @return an explanation; null if it cannot be explained
	 */
	public DeadFeatureExplanation getVoidFeatureModelExplanation() {
		return getVoidFeatureModelExplanation(fm);
	}

	/**
	 * Returns an explanation why the given feature model is void. That is the same explanation for why its root feature is dead.
	 *
	 * @param fm potentially void feature model; not null
	 * @return an explanation; null if it cannot be explained
	 */
	public DeadFeatureExplanation getVoidFeatureModelExplanation(IFeatureModel fm) {
		return getDeadFeatureExplanation(fm, FeatureUtils.getRoot(fm));
	}

	/**
	 * Returns an explanation why the given feature is dead.
	 *
	 * @param feature potentially dead feature; not null
	 * @return an explanation; null if it cannot be explained
	 */
	public DeadFeatureExplanation getDeadFeatureExplanation(IFeature feature) {
		return getDeadFeatureExplanation(fm, feature);
	}

	/**
	 * Adds an explanation why the given feature is dead.
	 *
	 * @param fm feature model containing the feature; not null
	 * @param feature potentially dead feature; not null
	 * @return an explanation; null if it cannot be explained
	 */
	public DeadFeatureExplanation getDeadFeatureExplanation(IFeatureModel fm, IFeature feature) {
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
		final DeadFeatureExplanationCreator creator;
		if (fm == this.fm) {
			creator = deadFeatureExplanationCreator;
		} else {
			creator = explanationCreatorFactory.getDeadFeatureExplanationCreator();
			creator.setFeatureModel(fm);
		}
		creator.setSubject(feature);
		deadFeatureExplanations.put(feature, creator.getExplanation());
	}

	/**
	 * Returns an explanation why the given feature is false-optional.
	 *
	 * @param feature potentially false-optional feature; not null
	 * @return an explanation; null if it cannot be explained
	 */
	public FalseOptionalFeatureExplanation getFalseOptionalFeatureExplanation(IFeature feature) {
		return getFalseOptionalFeatureExplanation(fm, feature);
	}

	/**
	 * Returns an explanation why the given feature is false-optional.
	 *
	 * @param fm feature model containing the feature; not null
	 * @param feature potentially false-optional feature; not null
	 * @return an explanation; null if it cannot be explained
	 */
	public FalseOptionalFeatureExplanation getFalseOptionalFeatureExplanation(IFeatureModel fm, IFeature feature) {
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
		final FalseOptionalFeatureExplanationCreator creator;
		if (fm == this.fm) {
			creator = falseOptionalFeatureExplanationCreator;
		} else {
			creator = explanationCreatorFactory.getFalseOptionalFeatureExplanationCreator();
			creator.setFeatureModel(fm);
		}
		creator.setSubject(feature);
		falseOptionalFeatureExplanations.put(feature, creator.getExplanation());
	}

	/**
	 * Returns an explanation why the given constraint is redundant.
	 *
	 * @param constraint potentially redundant constraint; not null
	 * @return an explanation; null if it cannot be explained
	 */
	public RedundantConstraintExplanation getRedundantConstraintExplanation(IConstraint constraint) {
		return getRedundantConstraintExplanation(fm, constraint);
	}

	/**
	 * Returns an explanation why the given constraint is redundant.
	 *
	 * @param constraint potentially redundant constraint; not null
	 * @return an explanation; null if it cannot be explained
	 */
	public RedundantConstraintExplanation getRedundantConstraintExplanation(IFeatureModel fm, IConstraint constraint) {
		if (!redundantConstraintExplanations.containsKey(constraint)) {
			addRedundantConstraintExplanation(fm, constraint);
		}
		return redundantConstraintExplanations.get(constraint);
	}

	/**
	 * <p> Adds an explanation why the given constraint is redundant. </p>
	 *
	 * <p> Uses the given feature model, which may differ from the default feature model stored in this instance. This is for example the case when explaining
	 * implicit constraints in subtree models. </p>
	 *
	 * @param fm feature model containing the constraint; not null
	 * @param constraint potentially redundant constraint; not null
	 */
	private void addRedundantConstraintExplanation(IFeatureModel fm, IConstraint constraint) {
		final RedundantConstraintExplanationCreator creator;
		if (fm == this.fm) {
			creator = redundantConstraintExplanationCreator;
		} else {
			creator = explanationCreatorFactory.getRedundantConstraintExplanationCreator();
			creator.setFeatureModel(fm);
		}
		creator.setSubject(constraint);
		redundantConstraintExplanations.put(constraint, creator.getExplanation());
	}

	/**
	 * Clears all explanations.
	 */
	public void clearExplanations() {
		deadFeatureExplanations.clear();
		falseOptionalFeatureExplanations.clear();
		redundantConstraintExplanations.clear();
		deadFeatureExplanationCreator.setFeatureModel(fm);
		falseOptionalFeatureExplanationCreator.setFeatureModel(fm);
		redundantConstraintExplanationCreator.setFeatureModel(fm);

	}

	public FeatureModelAnalyzer clone(IFeatureModel newFeatureModel) {
		return new FeatureModelAnalyzer(this, newFeatureModel);
	}
}
