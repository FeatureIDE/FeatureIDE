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
package de.ovgu.featureide.core.builder.preprocessor;

import static de.ovgu.featureide.fm.core.localization.StringTable.IS_DEFINED_AS_ABSTRACT_IN_THE_FEATURE_MODEL__ONLY_CONCRETE_FEATURES_SHOULD_BE_REFERENCED_IN_PREPROCESSOR_DIRECTIVES_;
import static de.ovgu.featureide.fm.core.localization.StringTable.IS_NOT_DEFINED_IN_THE_FEATURE_MODEL_AND_COMMA__THUS_COMMA__ALWAYS_ASSUMED_TO_BE_FALSE;
import static de.ovgu.featureide.fm.core.localization.StringTable.PREPROCESSOR;

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Scanner;
import java.util.Stack;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.NodeReader;
import org.prop4j.Not;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.explanations.preprocessors.InvariantPresenceConditionExplanation;
import de.ovgu.featureide.fm.core.explanations.preprocessors.InvariantPresenceConditionExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.preprocessors.PreprocessorExplanationCreatorFactory;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;

/**
 * Abstract class for FeatureIDE preprocessor composer extensions with predefined functions.
 *
 * @author Christoph Giesel
 * @author Marcus Kamieth
 * @author Marcus Pinnecke (Feature Interface)
 */
public abstract class PPComposerExtensionClass extends ComposerExtensionClass {

	/**
	 * The satisfiability status of an annotation.
	 *
	 * @author Christoph Giesel
	 * @author Timo G&uuml;nther
	 */
	public enum AnnotationStatus {
		/** The presence condition is satisfiable but not a tautology. */
		NORMAL,
		/** The feature model is void. */
		VOID,
		/** The presence condition is a contradiction, causing a dead code block. */
		DEAD,
		/** The presence condition is a tautology, making the annotation superfluous. */
		SUPERFLUOUS,
		/** The expression in and of itself is a contradiction, causing a dead code block. */
		CONTRADICTION,
		/** The expression in and of itself is a tautology, making the annotation superfluous. */
		TAUTOLOGY,
	}

	protected static final String MESSAGE_DEAD = "This annotation causes a dead code block.";
	protected static final String MESSAGE_SUPERFLUOUS = "This annotation is superfluous.";
	protected static final String MESSAGE_CONTRADICTION = "This expression is a contradiction and causes a dead code block.";
	protected static final String MESSAGE_TAUTOLOGY = "This expression is a tautology, making the annotation superfluous.";
	protected static final String MESSAGE_ABSTRACT =
		IS_DEFINED_AS_ABSTRACT_IN_THE_FEATURE_MODEL__ONLY_CONCRETE_FEATURES_SHOULD_BE_REFERENCED_IN_PREPROCESSOR_DIRECTIVES_;
	protected static final String MESSAGE_NOT_DEFINED = IS_NOT_DEFINED_IN_THE_FEATURE_MODEL_AND_COMMA__THUS_COMMA__ALWAYS_ASSUMED_TO_BE_FALSE;

	/** Creates explanations for expressions that are contradictions or tautologies. */
	private final InvariantPresenceConditionExplanationCreator invariantExpressionExplanationCreator =
		PreprocessorExplanationCreatorFactory.getDefault().getInvariantPresenceConditionExplanationCreator();

	/**
	 * Feature model node generated in {@link #performFullBuild(IFile)} and used for expression checking.
	 */
	protected Node featureModel;

	/**
	 * {@code true}, if the feature model is void, {@code false} otherwise
	 */
	protected boolean voidFeatureModel;

	/**
	 * Preprocessor name used for messages in build markers (must set in subclass).
	 */
	protected String pluginName = PREPROCESSOR;

	/**
	 * List of activated features. List will be generated in {@link #prepareFullBuild(IFile)}.
	 */
	protected ArrayList<String> activatedFeatures;

	/**
	 * List of all features from model as ArrayList. List will be generated in {@link #prepareFullBuild(IFile)}.
	 */
	protected Collection<String> featureList;

	/**
	 * Pattern for checking of concrete feature: "feature1|feature2|feature3|...".
	 */
	protected Pattern patternIsConcreteFeature;

	/**
	 * Pattern for checking of abstract feature: "feature1|feature2|feature3|...".
	 */
	protected Pattern patternIsAbstractFeature;

	/**
	 * Node Reader for parsing expressions in preprocessor annotations to check for tautologies and contradictions.
	 */
	protected NodeReader nodereader = new NodeReader();

	/**
	 * Stack for preprocessor directives (for nested expressions). Have to be initialized in subclass.
	 */
	protected Stack<Node> expressionStack;

	/**
	 * Stack for count of "if" and "else" instructions for each level. Have to be initialized in subclass.
	 */
	protected Stack<Integer> ifelseCountStack;

	private static final String BUILDER_MARKER = CorePlugin.PLUGIN_ID + ".builderProblemMarker";
	private static final String FEATURE_MODULE_MARKER = CorePlugin.PLUGIN_ID + ".featureModuleMarker";

	/** contains all used features at any source file **/
	protected HashSet<String> usedFeatures = new HashSet<>();

	/**
	 * Sets the name of the plug-in
	 */
	public PPComposerExtensionClass(String pluginName) {
		this.pluginName = pluginName;
	}

	/**
	 * Initializes class fields. Should called at start of {@link #performFullBuild(IFile)}.
	 *
	 * @param config Path to the activated configuration file.
	 * @return Return <code>false</code> if configuration file does not exists or its feature list is empty.
	 */
	public boolean prepareFullBuild(IFile config) {
		usedFeatures.clear();
		assert (featureProject != null) : "Invalid project given";
		if (config != null) {
			final String configPath = config.getRawLocation().toOSString();

			if (configPath == null) {
				return false;
			}

			// Fix for #625: Antenna has currently no implementation for .xml config files.
			final Configuration configurationFile = new Configuration(featureProject.getFeatureModel());
			ConfigurationManager.load(Paths.get(config.getRawLocationURI()), configurationFile);
			// // read activated features from configuration
			activatedFeatures = new ArrayList<String>(configurationFile.getSelectedFeatureNames());

		}
		// get all concrete and abstract features and generate pattern
		final StringBuilder concreteFeatures = new StringBuilder();
		final StringBuilder abstractFeatures = new StringBuilder();
		final IFeatureModel fm = featureProject.getFeatureModel();
		for (final IFeature feature : fm.getFeatures()) {
			if (feature.getStructure().isConcrete()) {
				concreteFeatures.append(feature.getName());
				concreteFeatures.append("|");
			} else {
				abstractFeatures.append(feature.getName());
				abstractFeatures.append("|");
			}
		}
		// checking if there are any abstract features
		if (abstractFeatures.length() > 0) {
			patternIsAbstractFeature = Pattern.compile(abstractFeatures.substring(0, abstractFeatures.length() - 1));
		}
		if (concreteFeatures.length() > 0) {
			patternIsConcreteFeature = Pattern.compile(concreteFeatures.substring(0, concreteFeatures.length() - 1));
		}

		// create expression of feature model
		featureModel = AdvancedNodeCreator.createNodes(fm);
		try {
			voidFeatureModel = !new SatSolver(featureModel, 1000).isSatisfiable();
		} catch (final TimeoutException e) {
			voidFeatureModel = false;
		}

		featureList = Functional.toList(FeatureUtils.extractFeatureNames(fm.getFeatures()));

		return true;
	}

	/**
	 * Checks the expression on top of the expression stack for a contradiction or a tautology. Does not set any markers.
	 *
	 * @return the status of the annotation
	 */
	protected AnnotationStatus isContradictionOrTautology() {
		final Node expression = expressionStack.peek();

		Node nestedExpressions = null;
		if (expressionStack.size() > 1) {
			Node[] children = expressionStack.toArray(new Node[expressionStack.size()]);
			children = Arrays.copyOfRange(children, 0, children.length - 1); // Exclude the topmost expression because it is examined separately.
			nestedExpressions = new And(children);
		}

		try {
			return isContradictionOrTautology(expression, featureModel, nestedExpressions);
		} catch (final TimeoutException e) {
			CorePlugin.getDefault().logError(e);
			return AnnotationStatus.NORMAL;
		}
	}

	private AnnotationStatus isContradictionOrTautology(Node expression, Node featureModel, Node nestedExpressions) throws TimeoutException {
		if (voidFeatureModel) {
			return AnnotationStatus.VOID;
		}

		/*
		 * -SAT(expression)
		 */
		if (!new SatSolver(expression, 1000).isSatisfiable()) {
			return AnnotationStatus.CONTRADICTION;
		}

		/*
		 * -SAT(-expression)
		 */
		if (!new SatSolver(new Not(expression), 1000).isSatisfiable()) {
			return AnnotationStatus.TAUTOLOGY;
		}

		Node context = featureModel;
		if (nestedExpressions != null) {
			context = new And(context, nestedExpressions);
		}

		/*
		 * -SAT(FM & nestedExpressions & expression)
		 */
		if (!new SatSolver(new And(context, expression), 1000).isSatisfiable()) {
			return AnnotationStatus.DEAD;
		}

		/*
		 * TAUT(FM & nestedExpressions => expression) = -SAT(-(FM & nestedExpressions => expression)) = -SAT(-(-(FM & nestedExpressions) | expression)) =
		 * -SAT(-(-FM | -nestedExpressions | expression)) = -SAT(FM & nestedExpressions & -expression)
		 */
		if (!new SatSolver(new And(context, new Not(expression)), 1000).isSatisfiable()) {
			return AnnotationStatus.SUPERFLUOUS;
		}

		return AnnotationStatus.NORMAL;
	}

	/**
	 * Set marker for tautology or contradiction on given line in given file.
	 *
	 * @param status the status of the annotation
	 * @param lineNumber number of line
	 * @param res file path
	 */
	protected void setMarkersOnContradictionOrTautology(AnnotationStatus status, int lineNumber, IFile res) {
		String message;
		switch (status) {
		case NORMAL:
		case VOID:
			return;
		case CONTRADICTION:
			message = MESSAGE_CONTRADICTION;
			break;
		case DEAD:
			message = MESSAGE_DEAD;
			break;
		case TAUTOLOGY:
			message = MESSAGE_TAUTOLOGY;
			break;
		case SUPERFLUOUS:
			message = MESSAGE_SUPERFLUOUS;
			break;
		default:
			throw new IllegalStateException("Unknown annotation status");
		}

		boolean positive = false;
		switch (status) {
		case SUPERFLUOUS:
			positive = true;
		case DEAD:
			final InvariantPresenceConditionExplanation explanation = getInvariantExpressionExplanation(positive);
			if ((explanation != null) && (explanation.getReasons() != null) && !explanation.getReasons().isEmpty()) {
				message += System.lineSeparator();
				message += explanation.getWriter().getString();
			}
			break;
		default:
			break;
		}

		featureProject.createBuilderMarker(res, message, lineNumber, IMarker.SEVERITY_WARNING);
	}

	/**
	 * Returns an explanation for why the expression currently on top of the expression stack is a contradiction or a tautology.
	 *
	 * @param tautology true if the expression to explain is a tautology; false if it is a contradiction
	 * @return an explanation
	 */
	private InvariantPresenceConditionExplanation getInvariantExpressionExplanation(boolean tautology) {
		invariantExpressionExplanationCreator.setFeatureModel(featureProject.getFeatureModel());
		final List<Node> reverseExpressionStack = new ArrayList<>(expressionStack);
		Collections.reverse(reverseExpressionStack); // Iteration order of Stack is from bottom to top instead of top to bottom.
		invariantExpressionExplanationCreator.setExpressionStack(reverseExpressionStack);
		invariantExpressionExplanationCreator.setTautology(tautology);
		return invariantExpressionExplanationCreator.getExplanation();
	}

	/**
	 * <p> Checks whether the expression in the given line is a tautology or a contradiction. If so, a marker is added to the given line. </p>
	 *
	 * <p> It is assumed that the expression to check is on top of the expression stack. </p>
	 *
	 * @param lineNumber line number of the expression
	 * @param res file containing the expression
	 */
	protected void checkContradictionOrTautology(int lineNumber, IFile res) {
		findLiterals(expressionStack.peek());
		final AnnotationStatus status = isContradictionOrTautology();
		setMarkersOnContradictionOrTautology(status, lineNumber, res);
	}

	private void findLiterals(Node ppExpression) {
		if (ppExpression instanceof Literal) {
			usedFeatures.add(((Literal) ppExpression).var.toString());
		} else {
			for (final Node child : ppExpression.getChildren()) {
				findLiterals(child);
			}
		}
	}

	/**
	 * Set marker if given feature does not exists or is abstract.
	 *
	 * @param name feature name
	 * @param lineNumber current line number
	 * @param res file containing the feature name
	 */
	protected boolean setMarkersOnNotExistingOrAbstractFeature(String name, int lineNumber, IFile res) {
		if (name == null) {
			return false;
		}

		Matcher matcherFeature = null;
		if (patternIsAbstractFeature != null) {
			matcherFeature = patternIsAbstractFeature.matcher(name);
		}

		if ((matcherFeature != null) && matcherFeature.matches()) {
			featureProject.createBuilderMarker(res, name + MESSAGE_ABSTRACT, lineNumber, IMarker.SEVERITY_WARNING);
		} else {
			Matcher matcherConreteFeature = null;
			if (patternIsConcreteFeature != null) {
				matcherConreteFeature = patternIsConcreteFeature.matcher(name);
			}

			if ((matcherConreteFeature != null) && !matcherConreteFeature.matches()) {
				featureProject.createBuilderMarker(res, name + MESSAGE_NOT_DEFINED, lineNumber, IMarker.SEVERITY_WARNING);
				return false;
			}
		}
		return true;
	}

	/**
	 * Read all lines of a file into a vector.
	 *
	 * @param res file path
	 * @return lines of the given file
	 */
	public static Vector<String> loadStringsFromFile(IFile res) {
		final Vector<String> lines = new Vector<String>();

		Scanner scanner = null;
		try {
			scanner = new Scanner(res.getContents(), "UTF-8");

			while (scanner.hasNext()) {
				lines.add(scanner.nextLine());
			}
		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(e);
		} finally {
			if (scanner != null) {
				scanner.close();
			}
		}
		return lines;
	}

	/**
	 *
	 */
	public void deleteAllPreprocessorAnotationMarkers() {
		try {
			final IFolder sourceFolder = featureProject.getComposer().hasFeatureFolder() ? featureProject.getSourceFolder() : featureProject.getBuildFolder();
			final IMarker[] markers = sourceFolder.findMarkers(BUILDER_MARKER, false, IResource.DEPTH_INFINITE);
			for (final IMarker marker : markers) {
				if (isPreprocessorAnotationMarker(marker)) {
					marker.delete();
				}
			}
		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * @param marker
	 * @return
	 * @throws CoreException
	 */
	private boolean isPreprocessorAnotationMarker(IMarker marker) throws CoreException {
		final String message = marker.getAttribute(IMarker.MESSAGE, "");
		if (message.contains(MESSAGE_ABSTRACT) || message.contains(MESSAGE_SUPERFLUOUS) || message.contains(MESSAGE_DEAD) || message.contains(MESSAGE_TAUTOLOGY)
			|| message.contains(MESSAGE_CONTRADICTION) || message.contains(MESSAGE_NOT_DEFINED)) {
			return true;
		}
		return false;
	}

	/**
	 * Creates following markers at the Feature Model:<br> -A Feature is never used in a preprocessor annotation<br> -A used Feature does not exist at the
	 * Feature Model<br> -A used Feature is abstract
	 */
	protected void setModelMarkers() {
		removeModelMarkers();
		final ArrayList<String> unusedConcrete = new ArrayList<>();
		final ArrayList<String> usedAbstract = new ArrayList<>();
		for (final IFeature f : featureProject.getFeatureModel().getFeatures()) {
			final String featureName = f.getName();
			if (f.getStructure().isConcrete()) {
				if (!usedFeatures.contains(featureName)) {
					unusedConcrete.add(featureName);
				}
			} else {
				if (usedFeatures.contains(featureName)) {
					usedAbstract.add(featureName);
				}
			}
		}

		if (!usedAbstract.isEmpty()) {
			Collections.sort(usedAbstract);
			final StringBuilder markerText = new StringBuilder("The following abstract features are referenced in the implementation: ");
			for (final String featureName : usedAbstract) {
				markerText.append("\"");
				markerText.append(featureName);
				markerText.append("\", ");
			}
			markerText.delete(markerText.length() - 2, markerText.length());
			createMarker(markerText.toString());
		}

		if (!unusedConcrete.isEmpty()) {
			Collections.sort(unusedConcrete);
			final StringBuilder markerText = new StringBuilder("The following concrete features are never referenced in the implementation: ");
			for (final String featureName : unusedConcrete) {
				markerText.append("\"");
				markerText.append(featureName);
				markerText.append("\", ");
			}
			markerText.delete(markerText.length() - 2, markerText.length());
			createMarker(markerText.toString());
		}
	}

	/**
	 * Removes the old model markers.
	 */
	private void removeModelMarkers() {
		try {
			featureProject.getModelFile().deleteMarkers(FEATURE_MODULE_MARKER, false, IResource.DEPTH_ZERO);
		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Creates a marker with the given message at the feature model.
	 *
	 * @param message
	 */
	private void createMarker(String message) {
		try {
			if (!hasMarker(message)) {
				final IMarker marker = featureProject.getModelFile().createMarker(FEATURE_MODULE_MARKER);
				marker.setAttribute(IMarker.MESSAGE, message);
				marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_WARNING);
				marker.setAttribute(IMarker.LINE_NUMBER, -1);
			}
		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Tests if the marker with the given message already exists.
	 *
	 * @param message
	 * @return
	 */
	private boolean hasMarker(String message) {
		try {
			for (final IMarker m : featureProject.getModelFile().findMarkers(FEATURE_MODULE_MARKER, false, IResource.DEPTH_ZERO)) {
				if (m.getAttribute(IMarker.MESSAGE, "").equals(message)) {
					return true;
				}
			}
		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		return false;
	}

	/**
	 * Further processing after the files are preprocessed.
	 *
	 * @param folder The folder containing the preprocessed files
	 */
	public void postProcess(IFolder folder) {}
}
