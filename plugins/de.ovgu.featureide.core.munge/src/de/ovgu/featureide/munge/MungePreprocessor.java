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
package de.ovgu.featureide.munge;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Stack;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.prop4j.And;
import org.prop4j.Node;
import org.prop4j.Not;
import org.sonatype.plugins.munge.Munge;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.preprocessor.PPComposerExtensionClass;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.munge.model.MungeModelBuilder;

/**
 * Munge: a purposely-simple Java preprocessor.
 * 
 * @author Jens Meinicke
 */
public class MungePreprocessor extends PPComposerExtensionClass{
	
	private MungeModelBuilder mungeModelBuilder;
	public static final String COMMENT_START = "/*";
	public static final String COMMENT_END = "*/";

	/** all allowed instructions in munge as regular expression */
	public static final String OPERATORS = "(if(_not)?|else|end)\\[(.+?)\\]";
	
	/** all allowed instructions in munge as compiled regular expression */
	public static final Pattern OP_PATTERN = Pattern.compile(OPERATORS);
	
	/** compiled regular expression for instructions and comment symbols */
	public static final Pattern OP_COM_PATTERN = Pattern.compile("(" + OPERATORS + ")|/\\*|\\*/");
	
	/** is true if actual line is in comment section (between <code>&#47;*</code> and <code>*&#47;</code>) */
	private boolean commentSection;
	
	public MungePreprocessor() {
		super("Munge");
	}
	
	@Override
	public boolean initialize(IFeatureProject project) {
		boolean supSuccess =super.initialize(project);
		if (mungeModelBuilder == null) {
			mungeModelBuilder = new MungeModelBuilder(project);
		}
		
		prepareFullBuild(null);
		annotationChecking();
		
		if(supSuccess==false||mungeModelBuilder==null) {
			return false;
		} else {
			return true;
		}
	}
	
	private static final LinkedHashSet<String> EXTENSIONS = createExtensions(); 
	
	private static LinkedHashSet<String> createExtensions() {
		LinkedHashSet<String> extensions = new LinkedHashSet<String>();
		extensions.add("java");
		return extensions;
	}  

	@Override
	public LinkedHashSet<String> extensions() {
		return EXTENSIONS;
	}

	@Override
	public void performFullBuild(IFile config) {
		if (!prepareFullBuild(config))
			return;
		try {
			preprocessSourceFiles(featureProject.getBuildFolder());
			annotationChecking();
		} catch (CoreException e) {
			MungeCorePlugin.getDefault().logError(e);
		}
		
		if (mungeModelBuilder != null)
			mungeModelBuilder.buildModel();
	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.ComposerExtensionClass#postModelChanged()
	 */
	@Override
	public void postModelChanged() {
		prepareFullBuild(null);
		annotationChecking();
	}

	private void annotationChecking() {
		deleteAllPreprocessorAnotationMarkers();
		Job job = new Job("preprocessor annotation checking") {
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				annotationChecking(featureProject.getSourceFolder());
				setModelMarkers();
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.SHORT);
		job.schedule();
	}
	
	private void annotationChecking(IFolder folder) {
		try {
			for (final IResource res : folder.members()) {
				if (res instanceof IFolder) {
					annotationChecking((IFolder)res);
				} else 
				if (res instanceof IFile){
					final Vector<String> lines = loadStringsFromFile((IFile) res);
					// do checking and some stuff
					processLinesOfFile(lines, (IFile) res);
				}
			}
		} catch (CoreException e) {
			MungeCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * preprocess all files in folder
	 * 
	 * @param sourceFolder folder with files to preprocess
	 * @param buildFolder folder for preprocessed files
	 * @param annotationChecking <code>true</code> if preprocessor annotations should be checked
	 * @param performFullBuild <code>true</code> if the munge should be called
	 * @throws CoreException
	 */
	private void preprocessSourceFiles(IFolder buildFolder) throws CoreException {
		LinkedList<String> args = new LinkedList<String>();
		for (String feature : activatedFeatures) {
			args.add("-D" + feature);
		}
		
		runMunge(args, featureProject.getSourceFolder(), buildFolder);
	}
	
	

	/**
	 * Calls munge for each package separate
	 * Creates all package folders at the build path
	 * @param featureArgs
	 * @param sourceFolder
	 * @param buildFolder
	 */
	private void runMunge(LinkedList<String> featureArgs, IFolder sourceFolder,
			IFolder buildFolder) {
		@SuppressWarnings("unchecked")
		LinkedList<String> packageArgs = (LinkedList<String>) featureArgs.clone();
		boolean added = false;
		try {
			createBuildFolder(buildFolder);
			for (final IResource res : sourceFolder.members()) {
				if (res instanceof IFolder) {
					runMunge(featureArgs, (IFolder)res, buildFolder.getFolder(res.getName()));
				} else 
				if (res instanceof IFile){
					added = true;
					packageArgs.add(res.getRawLocation().toOSString());
				}
			}
		} catch (CoreException e) {
			MungeCorePlugin.getDefault().logError(e);
		}
		if (!added) {
			return;
		}
		//add output directory
		packageArgs.add(buildFolder.getRawLocation().toOSString());
				
		//CommandLine syntax:
		//	-DFEATURE1 -DFEATURE2 ... File1 File2 ... outputDirectory
		runMunge(packageArgs);
	}

	/**
	 * Do checking for all lines of file.
	 * 
	 * @param lines all lines of file
	 * @param res file
	 */
	synchronized private void processLinesOfFile(Vector<String> lines, IFile res){
		expressionStack = new Stack<Node>();
		
		// count of if, ifelse and else to remove after processing of else from stack
		ifelseCountStack = new Stack<Integer>();
		ifelseCountStack.push(0);
		
		commentSection = false;
		
		// go line for line
		for (int j = 0; j < lines.size(); ++j) {
			String line = lines.get(j);
			
			if (line.contains("/*") || line.contains("*/") || commentSection) {
				
				setMarkersContradictionalFeatures(line, res, j+1);
				
				setMarkersNotConcreteFeatures(line, res, j+1);
			}
		}
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
	 * @param line content of line
	 * @param res file containing given line
	 * @param lineNumber line number of given line
	 */
	private void setMarkersContradictionalFeatures(String line, IFile res, int lineNumber){
		
		Matcher m = OP_COM_PATTERN.matcher(line);
		
		while (m.find()) {
			String completeElement = m.group(0);
			String singleElement = m.group(2);
			
			if (singleElement == null) {
				if (completeElement.equals("/*")) {
					commentSection = true;
				} else if (completeElement.equals("*/")) {
					commentSection = false;
				}
			} else {
				if (singleElement.startsWith("if") || singleElement.equals("else")) {
					if (singleElement.equals("else")) {
						if(!expressionStack.isEmpty()) {
							Node lastElement = new Not(expressionStack.pop().clone());
							expressionStack.push(lastElement);
						}
						
						Node[] nestedExpressions = new Node[expressionStack.size()];
						nestedExpressions = expressionStack.toArray(nestedExpressions);
						
						And nestedExpressionsAnd = new And(nestedExpressions);
						
						isContradictionOrTautology(nestedExpressionsAnd.clone(), true, lineNumber, res);
						
					} else {
						Node ppExpression = nodereader.stringToNode(m.group(4), featureList);
						
						if (singleElement.equals("if_not")) {
							ppExpression = new Not(ppExpression.clone());
						}
						
						if (singleElement.startsWith("if")) {
							ifelseCountStack.push(0);
						}
						
						ifelseCountStack.push(ifelseCountStack.pop() + 1);
						expressionStack.push(ppExpression);
						doThreeStepExpressionCheck(ppExpression, lineNumber, res);
					}
					
				} else if (singleElement.equals("end")) {
					for (; ifelseCountStack.peek() > 0; ifelseCountStack.push(ifelseCountStack.pop() - 1)) {
						if (!expressionStack.isEmpty())
							expressionStack.pop();
					}
					
					ifelseCountStack.pop();
				}
			}
		}
	}
	
	private void setMarkersNotConcreteFeatures(String line, IFile res, int lineNumber){
		Matcher matcherIf = OP_PATTERN.matcher(line);
		
		if (matcherIf.find()) {
			setMarkersOnNotExistingOrAbstractFeature(matcherIf.group(3), lineNumber, res);
		}
	}
	
	private void runMunge(LinkedList<String> args) {
		//convert into an Array
		String[] argArray = new String[args.size()];
		for (int i = 0;i < args.size();i++) {
			argArray[i] = args.get(i);
		}
		//run Munge
		Munge m = new Munge();
		m.main(argArray, featureProject);
	}

	private void createBuildFolder(IFolder buildFolder) throws CoreException {
		if (!buildFolder.exists()) {
			buildFolder.create(true, true, null);
		}
		buildFolder.refreshLocal(IResource.DEPTH_ZERO, null);
	}

	@Override
	public ArrayList<String[]> getTemplates() {
		return TEMPLATES;
	}
	
	private static final ArrayList<String[]> TEMPLATES = createTempltes();
	
	private static ArrayList<String[]> createTempltes() {
		 ArrayList<String[]> list = new  ArrayList<String[]>();
		 list.add(JAVA_TEMPLATE);
		 return list;
	}

	@Override
	public void postCompile(IResourceDelta delta, final IFile file) {
		super.postCompile(delta, file);
		Job job = new Job("Propagate problem markers") {
			@Override
			public IStatus run(IProgressMonitor monitor) {
				try {
					IMarker[] marker = file.findMarkers(null, false, IResource.DEPTH_ZERO);
					if (marker.length != 0) {
						for (IMarker m : marker) {
							IFile sourceFile = findSourceFile(file, featureProject.getSourceFolder());
							if (!hasMarker(m, sourceFile)) {
								IMarker newMarker = sourceFile.createMarker(CorePlugin.PLUGIN_ID + ".builderProblemMarker");
								newMarker.setAttribute(IMarker.LINE_NUMBER, m.getAttribute(IMarker.LINE_NUMBER));
								newMarker.setAttribute(IMarker.MESSAGE, m.getAttribute(IMarker.MESSAGE));
								newMarker.setAttribute(IMarker.SEVERITY, m.getAttribute(IMarker.SEVERITY));
							}
						}
					}
				} catch (CoreException e) {
					MungeCorePlugin.getDefault().logError(e);
				}
				return Status.OK_STATUS;
			}
			
			private boolean hasMarker(IMarker buildMarker, IFile sourceFile) {
				try {
					IMarker[] marker = sourceFile.findMarkers(null, true, IResource.DEPTH_ZERO);
					int LineNumber = buildMarker.getAttribute(IMarker.LINE_NUMBER, -1);
					String Message = buildMarker.getAttribute(IMarker.MESSAGE, null);
					if (marker.length > 0) {
						for (IMarker m : marker) {
							if (LineNumber == m.getAttribute(IMarker.LINE_NUMBER, -1)) {
								if (Message.equals(m.getAttribute(IMarker.MESSAGE, null))) {
									return true;
								}
							}
						}
					}
				} catch (CoreException e) {
					MungeCorePlugin.getDefault().logError(e);
				}
				return false;
			}
		};
		job.setPriority(Job.DECORATE);
		job.schedule();
	}
	
	private IFile findSourceFile(IFile file, IFolder folder) throws CoreException {
		for (IResource res: folder.members()) {
			if (res instanceof IFolder) {
				IFile sourceFile = findSourceFile(file, (IFolder)res);
				if (sourceFile != null) {
					return sourceFile;
				}
			} else if (res instanceof IFile) {
				if (res.getName().equals(file.getName()))
					return (IFile)res;
			}
		}
		return null;
	}

	@Override
	public boolean hasFeatureFolders() {
		return false;
	}
	
	@Override
	public void buildFSTModel() {
		mungeModelBuilder.buildModel();
	}
	
	@Override
	public void buildConfiguration(IFolder folder, Configuration configuration, String congurationName) {
		super.buildConfiguration(folder, configuration, congurationName);
		if (activatedFeatures == null) {
			activatedFeatures = new ArrayList<String>();
		} else {
			activatedFeatures.clear();
		}
		for (Feature feature : configuration.getSelectedFeatures()) {
			activatedFeatures.add(feature.getName());
		}
		try {
			preprocessSourceFiles(folder);
		} catch (CoreException e) {
			MungeCorePlugin.getDefault().logError(e);
		}
	}

	@Override
	public boolean showContextFieldsAndMethods() {
		return false;
	}

	@Override
	public LinkedList<FSTDirective> buildModelDirectivesForFile(Vector<String> lines) {
		return mungeModelBuilder.buildModelDirectivesForFile(lines);
	}
	
	@Override
	public boolean needColor() {
		return true;
	}


}
