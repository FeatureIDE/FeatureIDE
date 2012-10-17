/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.core.builder.preprocessor;

import java.util.ArrayList;
import java.util.LinkedList;
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
import org.prop4j.Implies;
import org.prop4j.Node;
import org.prop4j.NodeReader;
import org.prop4j.Not;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * Abstract class for FeatureIDE preprocessor composer extensions with predefined functions.
 * 
 * @author Christoph Giesel
 * @author Marcus Kamieth
 */
public abstract class PPComposerExtensionClass extends ComposerExtensionClass {
	
	/** The expression is satisfiable but not a tautology. */
	static final int SAT_NONE = 0;
	/** The expression is a contradiction. */
	static final int SAT_CONTRADICTION = 1;
	/** The expression is a tautology. */
	static final int SAT_TAUTOLOGY = 2;
	protected static final String MESSAGE_DEAD_CODE = ": This expression is dead code because it is always false.";
	protected static final String MESSAGE_ALWAYS_TRUE = ": This expression is always true.";
	protected static final String MESSAGE_ABSTRACT = " is defined as abstract in the feature model. Only concrete features should be referenced in preprocessor directives.";
	protected static final String MESSAGE_NOT_DEFINED = " is not defined in the feature model and thus always assumed to be false";

	/** Feature model node generated in {@link #performFullBuild(IFile)} and used for expression checking. */
	protected Node featureModel;
	
	/** Preprocessor name used for messages in build markers (must set in subclass). */
	protected String pluginName = "Preprocessor";
	
	/** List of activated features. List will be generated in {@link #prepareFullBuild(IFile)}. */
	protected ArrayList<String> activatedFeatures;
	
	/** List of all features from model as ArrayList. List will be generated in {@link #prepareFullBuild(IFile)}. */
	protected ArrayList<String> featureList;
	
	/** Pattern for checking of concrete feature: "feature1|feature2|feature3|...". */
	protected Pattern patternIsConcreteFeature;
	
	/** Pattern for checking of abstract feature: "feature1|feature2|feature3|...". */
	protected Pattern patternIsAbstractFeature;
	
	/** Node Reader for parsing expressions in preprocessor annotations to check for tautologies and contradictions. */
	protected NodeReader nodereader = new NodeReader();
	
	/** Stack for preprocessor directives (for nested expressions). Have to be initialized in subclass. */
	protected Stack<Node> expressionStack;
	
	/** Stack for count of "if" and "else" instructions for each level. Have to be initialized in subclass. */
	protected Stack<Integer> ifelseCountStack;
	
	private static final String BUILDER_MARKER = CorePlugin.PLUGIN_ID + ".builderProblemMarker";
	private static final String FEATURE_MODULE_MARKER = CorePlugin.PLUGIN_ID +".featureModuleMarker";
			
	/** contains all used features at any source file **/			
	protected LinkedList<String> usedFeatures = new LinkedList<String>();
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
	
			if (configPath == null)
				return false;

//			// read activated features from configuration
			activatedFeatures = new ArrayList<String>(loadStringsFromFile(config));

		}
		// get all concrete and abstract features and generate pattern
		StringBuilder concreteFeatures = new StringBuilder();
		StringBuilder abstractFeatures = new StringBuilder();
		for (Feature feature : featureProject.getFeatureModel().getFeatures()) {
			if (feature.isConcrete()) {
				concreteFeatures.append(feature.getName());
				concreteFeatures.append("|");
			} else {
				abstractFeatures.append(feature.getName());
				abstractFeatures.append("|");
			}
		}
		//checking if there are any abstract features
		if(abstractFeatures.length()>0)
		patternIsAbstractFeature = Pattern.compile(abstractFeatures.substring(0, abstractFeatures.length()-1));
		if(concreteFeatures.length()>0)
		patternIsConcreteFeature = Pattern.compile(concreteFeatures.substring(0, concreteFeatures.length()-1));
	
		// create expression of feature model
		featureModel = NodeCreator.createNodes(featureProject.getFeatureModel());
		
		featureList = new ArrayList<String>(featureProject.getFeatureModel().getFeatureNames());
		
		return true;
	}

	/**
	 * Checks expression for contradiction or tautology.
	 * 
	 * @param node the expression to prove
	 * @param withModel Checking with model if is <code>true</code>.
	 * @return {@link #SAT_CONTRADICTION}, {@link #SAT_TAUTOLOGY} or {@link #SAT_NONE}
	 */
	protected int isContradictionOrTautology(Node node, boolean withModel) {
		// with model: node
		// without model: feature model && node
		Node contradictionNode = ( withModel && featureModel != null ) ? new And(featureModel.clone(), node.clone()) : node.clone();
		// with model: !node
		// without model: !(feature model => node)
		Node tautologyNode = new Not(( withModel && featureModel != null ) ? new Implies(featureModel.clone(), node.clone()) : node.clone());
		
		// expression -> contradiction?
		SatSolver solverContradiction = new SatSolver(contradictionNode, 1000);
		// expression -> tautology?
		SatSolver solverTautology = new SatSolver(tautologyNode, 1000);
		
		try {
			if(!solverContradiction.isSatisfiable()){
				return SAT_CONTRADICTION;
			} else if(!solverTautology.isSatisfiable()){
				return SAT_TAUTOLOGY;
			}
		} catch (TimeoutException e) {
			CorePlugin.getDefault().logError(e);
		}
		
		return SAT_NONE;
	}
	
	/**
	 * Set marker for tautology or contradiction on given line in given file.
	 * 
	 * @param status expects {@link #SAT_CONTRADICTION} or {@link #SAT_TAUTOLOGY}.
	 * @param lineNumber number of line
	 * @param res file path
	 */
	protected void setMarkersOnContradictionOrTautology(int status, int lineNumber, IFile res) {
		if (status == SAT_CONTRADICTION) {
			featureProject.createBuilderMarker(res,
					pluginName + MESSAGE_DEAD_CODE, lineNumber,
					IMarker.SEVERITY_WARNING);
		} else if (status == SAT_TAUTOLOGY) {
			featureProject.createBuilderMarker(res,
					pluginName + MESSAGE_ALWAYS_TRUE, lineNumber,
					IMarker.SEVERITY_WARNING);
		}
	}
	
	/**
	 * Checks for tautology and contradiction and set build markers.
	 * 
	 * @param node expression to check.
	 * @param withModel Checking with model if is <code>true</code>.
	 * @param lineNumber number of line
	 * @param res file path
	 * @return {@link #SAT_CONTRADICTION}, {@link #SAT_TAUTOLOGY} or {@link #SAT_NONE}
	 */
	protected int isContradictionOrTautology(Node node, boolean withModel, int lineNumber, IFile res) {
		int status =  isContradictionOrTautology(node, withModel);
		
		setMarkersOnContradictionOrTautology(status, lineNumber, res);
		
		return status;
	}
	
	/**
	 * Checks given line if it contains expressions which are always 
	 * <code>true</code> or <code>false</code>.<br /><br />
	 * 
	 * Check in three steps:
	 * <ol>
	 * <li>just the given line</li>
	 * <li>the given line and the feature model</li>
	 * <li>the given line, the surrounding lines and the feature model</li>
	 * </ol>
	 * 
	 * @param ppExpression expression in the current line
	 * @param lineNumber line number
	 * @param res file containing the given expression
	 */
	protected void doThreeStepExpressionCheck(Node ppExpression, int lineNumber, IFile res) {
		if (ppExpression == null) {
			return;
		}

		/** collect all used features **/
		if (!usedFeatures.contains(ppExpression.toString())) {
			usedFeatures.add(ppExpression.toString());
		}
		
		int result = isContradictionOrTautology(ppExpression.clone(), false, lineNumber, res);
		
		if (result == SAT_NONE) {
			result = isContradictionOrTautology(ppExpression.clone(), true, lineNumber, res);
			
			if (result == SAT_NONE && !expressionStack.isEmpty()) {
				Node[] nestedExpressions = new Node[expressionStack.size()];
				nestedExpressions = expressionStack.toArray(nestedExpressions);
				
				And nestedExpressionsAnd = new And(nestedExpressions);
				
				isContradictionOrTautology(nestedExpressionsAnd.clone(), true, lineNumber, res);
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
	protected void setMarkersOnNotExistingOrAbstractFeature(String name, int lineNumber, IFile res) {
		if (name == null)
			return;

		Matcher matcherFeature =null;
		if(patternIsAbstractFeature!=null)
		matcherFeature = patternIsAbstractFeature.matcher(name);
		
		if (matcherFeature!=null&&matcherFeature.matches()) {
			featureProject.createBuilderMarker(res,
					pluginName + ": " + name +
						MESSAGE_ABSTRACT,
					lineNumber,
					IMarker.SEVERITY_WARNING);
		} else {
			Matcher matcherConreteFeature=null;;
			if(patternIsConcreteFeature!=null)
			matcherConreteFeature = patternIsConcreteFeature.matcher(name);
			
			if(matcherConreteFeature!=null&&!matcherConreteFeature.matches()) {
				featureProject.createBuilderMarker(res,
						pluginName + ": " + name +
							MESSAGE_NOT_DEFINED,
						lineNumber,
						IMarker.SEVERITY_WARNING);
			}
		}
	}
	
	/**
	 * Read all lines of a file into a vector.
	 * 
	 * @param res file path
	 * @return lines of the given file
	 */
	public static Vector<String> loadStringsFromFile(IFile res) {
		Vector<String> lines = new Vector<String>();
		
		Scanner scanner = null;
		try {
			scanner = new Scanner(res.getContents(), "UTF-8");
			
			while (scanner.hasNext()) {
				lines.add(scanner.nextLine());
			}
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		} finally {
			if (scanner != null)
				scanner.close();
		}
		return lines;
	}
	
	/**
	 * 
	 */
	public void deleteAllPreprocessorAnotationMarkers() {
		try {
			IFolder sourceFolder = featureProject.getComposer().hasFeatureFolder() ? featureProject.getSourceFolder() :
				featureProject.getBuildFolder();
			IMarker[] markers = sourceFolder.findMarkers(BUILDER_MARKER, false, IResource.DEPTH_INFINITE);
			for (IMarker marker : markers) {
				if (isPreprocessorAnotationMarker(marker)) {
					marker.delete();
				}
			}
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * @param marker 
	 * @return
	 * @throws CoreException 
	 */
	private boolean isPreprocessorAnotationMarker(IMarker marker) throws CoreException {
		String message = marker.getAttribute(IMarker.MESSAGE, "");
		if (message.contains(MESSAGE_ABSTRACT) ||
			message.contains(MESSAGE_ALWAYS_TRUE) ||
			message.contains(MESSAGE_DEAD_CODE) ||
			message.contains(MESSAGE_NOT_DEFINED)) {
				return true;
		}
		return false;
	}
	
	/**
	 * Creates following markers at the Feature Model:<br>
	 * -A Feature is never used in a preprocessor annotation<br>
	 * -A used Feature does not exist at the Feature Model<br>
	 * -A used Feature is abstract 
	 */
	@SuppressWarnings("unchecked")
	protected void setModelMarkers() {
		removeModelMarkers();
		LinkedList<String> features = (LinkedList<String>)this.usedFeatures.clone() ;
		for (Feature f : featureProject.getFeatureModel().getFeatures()) {
			if (f.isAbstract() && features.contains(f.getName())) {
				features.remove(f.getName());				
				createMarker("The Feature \"" + f.getName() + "\" needs to be concrete.");
			} else if (f.isConcrete() && !features.contains(f.getName())) {
				createMarker("You should use the Feature \"" + f.getName() + "\" or set it abstract.");
			} else {
				features.remove(f.getName());
			}
		}
		for (String f : features) {
			createMarker("You should create a Feature named \"" + f + "\".");
		}
	}

	/**
	 * Removes the old model markers.
	 */
	private void removeModelMarkers() {
		try {
			featureProject.getModelFile().deleteMarkers(FEATURE_MODULE_MARKER, false, IResource.DEPTH_ZERO);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Creates a marker with the given message at the feature model.
	 * @param message
	 */
	private void createMarker(String message) {
		try {
			if (!hasMarker(message)) {
				IMarker marker = featureProject.getModelFile().createMarker(FEATURE_MODULE_MARKER);
				marker.setAttribute(IMarker.MESSAGE, message);
				marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_WARNING);
				marker.setAttribute(IMarker.LINE_NUMBER, -1);
			}
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Tests if the marker with the given message already exists.
	 * @param message
	 * @return
	 */
	private boolean hasMarker(String message) {
		try {
			for (IMarker m : featureProject.getModelFile().findMarkers(FEATURE_MODULE_MARKER, false, IResource.DEPTH_ZERO)) {
				if (m.getAttribute(IMarker.MESSAGE, "").equals(message)) {
					return true;
				}
			}
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		return false;
	}
}
