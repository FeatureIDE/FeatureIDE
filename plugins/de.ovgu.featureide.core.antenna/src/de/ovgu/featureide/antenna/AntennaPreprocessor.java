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
package de.ovgu.featureide.antenna;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Stack;
import java.util.Vector;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;
import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;

import antenna.preprocessor.v3.PPException;
import antenna.preprocessor.v3.Preprocessor;
import de.ovgu.featureide.antenna.model.AntennaModelBuilder;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.preprocessor.PPComposerExtensionClass;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * Antenna: a purposely-simple Java preprocessor.
 * 
 * @author Christoph Giesel
 * @author Marcus Kamieth
 */
// TODO #413 implement buildConfiguration
public class AntennaPreprocessor extends PPComposerExtensionClass {

	/** antenna preprocessor used from external library */
	private Preprocessor preprocessor;

	private AntennaModelBuilder antennaModelBuilder;
	
	/** pattern for replacing preprocessor commands like "//#if" */
	static final Pattern replaceCommandPattern = Pattern.compile("//#(.+?)\\s");
	
	public AntennaPreprocessor() {
		super("Antenna");
	}

	@Override
	public boolean initialize(IFeatureProject project) {
		super.initialize(project);
		if (antennaModelBuilder == null) {
			antennaModelBuilder = new AntennaModelBuilder(project);
		}
		preprocessor = new Preprocessor(new AntennaLogger(),
				new AntennaLineFilter());

		if (project.getProjectSourcePath() == null
				|| project.getProjectSourcePath().equals("")) {
			project.setPaths(project.getBuildPath(), project.getBuildPath(),
					project.getConfigPath());
		}
		return true;
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

		// generate comma separated string of activated features
		StringBuilder featureList = new StringBuilder();
		for (String feature : activatedFeatures) {
			featureList.append(feature + ",");
		}
		if(featureList.length()>0)
		featureList.deleteCharAt(featureList.length()-1);

		// add source files
		try {
			// add activated features as definitions to preprocessor
			preprocessor.addDefines(featureList.toString());

			// preprocess for all files in source folder
			startPreprocessingSourceFiles(featureProject.getBuildFolder(), true);
		} catch (Exception e) {
			AntennaCorePlugin.getDefault().logError(e);
		}

		if (antennaModelBuilder != null)
			antennaModelBuilder.buildModel();
	}

	/*
	 * buildFile is not set to derived
	 * 
	 * @see
	 * de.ovgu.featureide.core.builder.ComposerExtensionClass#postCompile(org
	 * .eclipse.core.resources.IResourceDelta, org.eclipse.core.resources.IFile)
	 */
	@Override
	public void postCompile(IResourceDelta delta, IFile buildFile) {
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.ComposerExtensionClass#postModelChanged()
	 */
	@Override
	public void postModelChanged() {
			deleteAllPreprocessorAnotationMarkers();
			prepareFullBuild(null);
			startPreprocessingSourceFiles(featureProject.getBuildFolder(), false);
	}
	
	private void startPreprocessingSourceFiles(IFolder sourceFolder, boolean performFullBuild) {
		try {
			preprocessSourceFiles(sourceFolder, performFullBuild);
			setModelMarkers();
		} catch (FileNotFoundException e) {
			AntennaCorePlugin.getDefault().logError(e);
		} catch (CoreException e) {
			AntennaCorePlugin.getDefault().logError(e);
		} catch (IOException e) {
			AntennaCorePlugin.getDefault().logError(e);
		}
	}
	/**
	 * preprocess all files in folder
	 * 
	 * @param sourceFolder folder with files to preprocess
	 * @throws CoreException
	 * @throws FileNotFoundException
	 * @throws IOException
	 */
	private void preprocessSourceFiles(IFolder sourceFolder, boolean performFullBuild) throws CoreException,
			FileNotFoundException, IOException {
		for (final IResource res : sourceFolder.members()) {
			if (res instanceof IFolder) {
				// for folders do recursively 
				preprocessSourceFiles((IFolder) res, performFullBuild);
			} else if (res instanceof IFile) {
				// delete all existing builder markers 
				if (performFullBuild) {
					featureProject.deleteBuilderMarkers(res, 0);
				}
				
				// get all lines from file
				final Vector<String> lines = loadStringsFromFile((IFile) res);
				
				// do checking and some stuff
				processLinesOfFile(lines, (IFile) res);
				
				if (!performFullBuild) {
					continue;
				}

				boolean changed = false;

				try {
					// run antenna preprocessor
					changed = preprocessor.preprocess(lines,
							((IFile) res).getCharset());
				} catch (PPException e) {
					featureProject.createBuilderMarker(
							res,
							e.getMessage().replace(
									"Line #" + e.getLineNumber() + " :",
									"Antenna:"), e.getLineNumber() + 1,
							IMarker.SEVERITY_ERROR);
					AntennaCorePlugin.getDefault().logError(e);
				}

				// if preprocessor changed file: save & refresh
				if (changed) {
					FileOutputStream ostr = null;
					try {
						ostr = new FileOutputStream(res
								.getRawLocation().toOSString());
						Preprocessor.saveStrings(lines, ostr,
								((IFile) res).getCharset());
					} finally {
						if (ostr != null) {
							ostr.close();
						}
					}
					// use touch to support e.g. linux
					res.touch(null);
					res.refreshLocal(IResource.DEPTH_ZERO, null);
				}
			}
		}
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
		
		// go line for line
		for (int j = 0; j < lines.size(); ++j) {
			String line = lines.get(j);
			
			// if line is preprocessor directive
			if (line.contains("//#")) {
				if (line.contains("//#if ") ||
					line.contains("//#elif ") ||
					line.contains("//#condition ") ||
					line.contains("//#ifdef ") ||
					line.contains("//#ifndef ") ||
					line.contains("//#elifdef ") ||
					line.contains("//#elifndef ") ||
					line.contains("//#else")) {
					
					// if e1, elseif e2, ..., elseif en  ==  if -e1 && -e2 && ... && en
					// if e1, elseif e2, ..., else  ==  if -e1 && -e2 && ...
					if (line.contains("//#elif ") || line.contains("//#elifdef ") || line.contains("//#elifndef ") || line.contains("//#else")) {
						if(!expressionStack.isEmpty()) {
							Node lastElement = new Not(expressionStack.pop().clone());
							expressionStack.push(lastElement);
						}
					} else if (line.contains("//#if ") || line.contains("//#ifdef ") || line.contains("//#ifndef ")) {
						ifelseCountStack.push(0);
					}
					
					if (!ifelseCountStack.empty() && !line.contains("//#else"))
						ifelseCountStack.push(ifelseCountStack.pop() + 1);
					
					setMarkersContradictionalFeatures(line, res, j+1);
					
					setMarkersNotConcreteFeatures(line, res, j+1);
				} else if (line.contains("//#endif")) {
					while (!ifelseCountStack.empty()) {
						if (ifelseCountStack.peek() == 0)
							break;
						
						if (!expressionStack.isEmpty())
							expressionStack.pop();
						
						ifelseCountStack.push(ifelseCountStack.pop() - 1);
					}
					
					if (!ifelseCountStack.empty())
						ifelseCountStack.pop();
				}
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
		if (line.contains("//#else")) {
			if (!expressionStack.isEmpty()) {
				Node[] nestedExpressions = new Node[expressionStack.size()];
				nestedExpressions = expressionStack.toArray(nestedExpressions);
				
				And nestedExpressionsAnd = new And(nestedExpressions);
				
				isContradictionOrTautology(nestedExpressionsAnd.clone(), true, lineNumber, res);
			}
			
			return;
		}
		
		boolean conditionIsSet = line.contains("//#condition ");
		boolean negative = line.contains("//#ifndef ") || line.contains("//#elifndef ");
		
		// remove "//#if ", "//ifdef", ...
		line = replaceCommandPattern.matcher(line).replaceAll("");
		
		// prepare expression for NodeReader()
		line = line.trim();
		line = line.replace("&&", "&");
		line = line.replace("||", "|");
		line = line.replace("!", "-");
		line = line.replace("&", " and ");
		line = line.replace("|", " or ");
		line = line.replace("-", " not ");
		
		//get all features and generate Node expression for given line
		Node ppExpression = nodereader.stringToNode(line, featureList);
		
		if (ppExpression != null) {
			if (negative)
				ppExpression = new Not(ppExpression.clone());
			
			if (!conditionIsSet)
				expressionStack.push(ppExpression);
			
			doThreeStepExpressionCheck(ppExpression, lineNumber, res);
		} else {
			// if generating of expression failed, generate expression "true"
			if (!conditionIsSet)
				expressionStack.push(new Literal(NodeCreator.varTrue));
		}
		
	}
	
	/**
	 * Checks given line if it contains not existing or abstract features.
	 * 
	 * @param line content of line
	 * @param res file containing given line
	 * @param lineNumber line number of given line
	 */
	private void setMarkersNotConcreteFeatures(String line, IFile res, int lineNumber) {
		String[] splitted = line.split(AntennaModelBuilder.OPERATORS, 0);
		
		for (int i = 0; i < splitted.length; ++i) {
			if (!splitted[i].equals("") && !splitted[i].contains("//#")) {
				setMarkersOnNotExistingOrAbstractFeature(splitted[i], lineNumber, res);
			}
		}
	}
	
	@Override
	public ArrayList<String[]> getTemplates() {
		return TEMPLATES;
	}
	
	private static final ArrayList<String[]> TEMPLATES = createTempltes();
	
	private static ArrayList<String[]> createTempltes() {
		 ArrayList<String[]> list = new  ArrayList<String[]>(1);
		 list.add(JAVA_TEMPLATE);
		 return list;
	}

	@Override
	public boolean clean() {
		return false;
	}

	@Override
	public boolean hasFeatureFolders() {
		return false;
	}

	@Override
	public boolean hasFeatureFolder() {
		return false;
	}

	@Override
	public void copyNotComposedFiles(IFile config, IFolder destination) {
		
	}

	@Override
	public void buildFSTModel() {
		antennaModelBuilder.buildModel();
	}
	
	@Override
	public boolean postAddNature(IFolder source, IFolder destination) {
		return true;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.IComposerExtensionClass#showContextFieldsAndMethods()
	 */
	@Override
	public boolean showContextFieldsAndMethods() {
		return false;
	}
	
	@Override
	public LinkedList<FSTDirective> buildModelDirectivesForFile(Vector<String> lines) {
		return antennaModelBuilder.buildModelDirectivesForFile(lines);
	}

	@Override
	public boolean needColor() {
		return true;
	}

}
