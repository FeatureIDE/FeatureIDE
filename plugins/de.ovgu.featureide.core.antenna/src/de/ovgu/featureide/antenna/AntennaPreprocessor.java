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
package de.ovgu.featureide.antenna;

import static de.ovgu.featureide.fm.core.localization.StringTable.ANTENNA;
import static de.ovgu.featureide.fm.core.localization.StringTable.PROPAGATE_PROBLEM_MARKERS_FOR;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Stack;
import java.util.Vector;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IContainer;
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
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;

import antenna.preprocessor.v3.PPException;
import antenna.preprocessor.v3.Preprocessor;
import de.ovgu.featureide.antenna.documentation.DocumentationCommentParser;
import de.ovgu.featureide.antenna.model.AntennaModelBuilder;
import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.core.builder.IComposerObject;
import de.ovgu.featureide.core.builder.preprocessor.PPComposerExtensionClass;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.core.signature.documentation.base.ADocumentationCommentParser;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * Antenna: a purposely-simple Java preprocessor.
 *
 * @author Christoph Giesel
 * @author Marcus Kamieth
 * @author Marcus Pinnecke (Feature Interface)
 * @author Christopher Sontag
 */
public class AntennaPreprocessor extends PPComposerExtensionClass {

	/** antenna preprocessor used from external library */
	private Preprocessor preprocessor;

	private AntennaModelBuilder antennaModelBuilder;

	/** pattern for replacing preprocessor commands like "//#if" */
	static final Pattern replaceCommandPattern = Pattern.compile("//\\s*\\#(.+?)\\s");

	public AntennaPreprocessor() {
		super(ANTENNA);
		nodereader.setIgnoreMissingFeatures(true);
		nodereader.setIgnoreUnparsableSubExpressions(true);
	}

	@Override
	public boolean initialize(IFeatureProject project) {
		super.initialize(project);
		antennaModelBuilder = new AntennaModelBuilder(project);
		preprocessor = new Preprocessor(new AntennaLogger(), new AntennaLineFilter());

		final String projectSourcePath = project.getProjectSourcePath();
		if ((projectSourcePath == null) || projectSourcePath.isEmpty()) {
			final String buildPath = project.getBuildPath();
			project.setPaths(buildPath, buildPath, project.getConfigPath());
		}
		return true;
	}

	private static final LinkedHashSet<String> EXTENSIONS = createExtensions();

	private static LinkedHashSet<String> createExtensions() {
		final LinkedHashSet<String> extensions = new LinkedHashSet<String>();
		extensions.add("java");
		return extensions;
	}

	@Override
	public LinkedHashSet<String> extensions() {
		return EXTENSIONS;
	}

	@Override
	public void performFullBuild(IFile config) {
		if (!prepareFullBuild(config)) {
			return;
		}

		// generate comma separated string of activated features
		final StringBuilder featureList = new StringBuilder();
		for (final String feature : activatedFeatures) {
			featureList.append(feature + ",");
		}
		final int length = featureList.length();
		if (length > 0) {
			featureList.deleteCharAt(length - 1);
		}

		// add source files
		try {
			// add activated features as definitions to preprocessor
			preprocessor.clearDefines();
			preprocessor.addDefines(featureList.toString());

			// preprocess for all files in source folder
			startPreprocessingSourceFiles(featureProject.getBuildFolder(), true);
		} catch (final Exception e) {
			AntennaCorePlugin.getDefault().logError(e);
		}

		if (antennaModelBuilder != null) {
			antennaModelBuilder.buildModel();
		}
	}

	@Override
	public void postCompile(IResourceDelta delta, final IFile file) {
		if (isSourceFile(file.getParent())) {
			return;
		}
		super.postCompile(delta, file);
		final Job job =
			new Job((PROPAGATE_PROBLEM_MARKERS_FOR + CorePlugin.getFeatureProject(file)) != null ? CorePlugin.getFeatureProject(file).toString() : "") {

				@Override
				public IStatus run(IProgressMonitor monitor) {
					try {
						final IMarker[] marker = file.findMarkers(null, false, IResource.DEPTH_ZERO);
						if (marker.length != 0) {
							for (final IMarker m : marker) {
								final IFile sourceFile = findSourceFile(file, featureProject.getBuildFolder());
								if (sourceFile == null) {
									AntennaCorePlugin.getDefault()
											.logWarning("Source file for " + file + " not found for project " + featureProject.getProjectName());
									continue;
								}
								if (!hasMarker(m, sourceFile)) {
									final IMarker newMarker = sourceFile.createMarker(CorePlugin.PLUGIN_ID + ".builderProblemMarker");
									newMarker.setAttribute(IMarker.LINE_NUMBER, m.getAttribute(IMarker.LINE_NUMBER));
									newMarker.setAttribute(IMarker.MESSAGE, m.getAttribute(IMarker.MESSAGE));
									newMarker.setAttribute(IMarker.SEVERITY, m.getAttribute(IMarker.SEVERITY));
								}
							}
						}
					} catch (final CoreException e) {
						AntennaCorePlugin.getDefault().logError(e);
					}
					return Status.OK_STATUS;
				}

				private boolean hasMarker(IMarker buildMarker, IFile sourceFile) {
					try {
						final IMarker[] marker = sourceFile.findMarkers(null, true, IResource.DEPTH_ZERO);
						final int LineNumber = buildMarker.getAttribute(IMarker.LINE_NUMBER, -1);
						final String Message = buildMarker.getAttribute(IMarker.MESSAGE, null);
						if (marker.length > 0) {
							for (final IMarker m : marker) {
								if (LineNumber == m.getAttribute(IMarker.LINE_NUMBER, -1)) {
									if (Message.equals(m.getAttribute(IMarker.MESSAGE, null))) {
										return true;
									}
								}
							}
						}
					} catch (final CoreException e) {
						AntennaCorePlugin.getDefault().logError(e);
					}
					return false;
				}

				private IFile findSourceFile(IFile file, IFolder folder) throws CoreException {
					for (final IResource res : folder.members()) {
						if (res instanceof IFolder) {
							final IFile sourceFile = findSourceFile(file, (IFolder) res);
							if (sourceFile != null) {
								return sourceFile;
							}
						} else if (res instanceof IFile) {
							if (res.getName().equals(file.getName())) {
								return (IFile) res;
							}
						}
					}
					return null;
				}
			};
		job.setPriority(Job.DECORATE);
		job.schedule();
	}

	/**
	 * Checks whether the file is contained in the source folder.
	 */
	private boolean isSourceFile(IContainer parent) {
		if (parent.equals(featureProject.getBuildFolder())) {
			return true;
		}
		if (parent instanceof IFolder) {
			return isSourceFile(parent.getParent());
		}
		return false;
	}

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
		} catch (final FileNotFoundException e) {
			AntennaCorePlugin.getDefault().logError(e);
		} catch (final CoreException e) {
			AntennaCorePlugin.getDefault().logError(e);
		} catch (final IOException e) {
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
	private void preprocessSourceFiles(IFolder sourceFolder, boolean performFullBuild) throws CoreException, FileNotFoundException, IOException {
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
					changed = preprocessor.preprocess(lines, ((IFile) res).getCharset());
				} catch (final PPException e) {
					final int lineNumber = e.getLineNumber();
					featureProject.createBuilderMarker(res, e.getMessage().replace("Line #" + lineNumber + " :", "Antenna:"), Math.max(lineNumber, 0) + 1,
							IMarker.SEVERITY_ERROR);
					AntennaCorePlugin.getDefault().logError(e);
				}

				// if preprocessor changed file: save & refresh
				if (changed) {
					FileOutputStream ostr = null;
					try {
						ostr = new FileOutputStream(res.getRawLocation().toOSString());
						Preprocessor.saveStrings(lines, ostr, ((IFile) res).getCharset());
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
	synchronized private void processLinesOfFile(Vector<String> lines, IFile res) {
		expressionStack = new Stack<Node>();

		// count of if, ifelse and else to remove after processing of else from stack
		ifelseCountStack = new Stack<Integer>();

		// go line for line
		for (int j = 0; j < lines.size(); ++j) {
			final String line = lines.get(j);

			// if line is preprocessor directive
			if (containsPreprocessorDirective(line, "ifdef|ifndef|condition|elifdef|elifndef|if|else|elif")) {

				// if e1, elseif e2, ..., elseif en == if -e1 && -e2 && ... && en
				// if e1, elseif e2, ..., else == if -e1 && -e2 && ...
				if (containsPreprocessorDirective(line, "elifdef|elifndef|else|elif")) {
					if (!expressionStack.isEmpty()) {
						final Node lastElement = new Not(expressionStack.pop().clone());
						expressionStack.push(lastElement);
					}
				} else if (containsPreprocessorDirective(line, "ifdef|ifndef|condition|if")) {
					ifelseCountStack.push(0);
				}

				if (!ifelseCountStack.empty() && !containsPreprocessorDirective(line, "else")) {
					ifelseCountStack.push(ifelseCountStack.pop() + 1);
				}

				setMarkersContradictionalFeatures(line, res, j + 1);

				setMarkersNotConcreteFeatures(line, res, j + 1);
			} else if (containsPreprocessorDirective(line, "endif")) {
				while (!ifelseCountStack.empty()) {
					if (ifelseCountStack.peek() == 0) {
						break;
					}

					if (!expressionStack.isEmpty()) {
						expressionStack.pop();
					}

					ifelseCountStack.push(ifelseCountStack.pop() - 1);
				}

				if (!ifelseCountStack.empty()) {
					ifelseCountStack.pop();
				}
			}
		}
	}

	/**
	 * Checks given line if it contains expressions which are always <code>true</code> or <code>false</code>.<br /> <br />
	 *
	 * Check in three steps: <ol> <li>just the given line</li> <li>the given line and the feature model</li> <li>the given line, the surrounding lines and the
	 * feature model</li> </ol>
	 *
	 * @param line content of line
	 * @param res file containing given line
	 * @param lineNumber line number of given line
	 */
	private void setMarkersContradictionalFeatures(String line, IFile res, int lineNumber) {
		if (containsPreprocessorDirective(line, "else")) {
			if (!expressionStack.isEmpty()) {
				checkContradictionOrTautology(lineNumber, res);
			}

			return;
		}

		final boolean conditionIsSet = containsPreprocessorDirective(line, "condition");
		final boolean negative = containsPreprocessorDirective(line, "ifndef|elifndef");

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

		// get all features and generate Node expression for given line
		Node ppExpression = nodereader.stringToNode(line, featureList);

		if (ppExpression != null) {
			if (negative) {
				ppExpression = new Not(ppExpression.clone());
			}
			expressionStack.push(ppExpression);

			checkContradictionOrTautology(lineNumber, res);
		} else {
			// if generating of expression failed, generate expression "true"
			if (!conditionIsSet) {
				expressionStack.push(new Literal(NodeCreator.varTrue));
			}
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
		final String[] splitted = line.replaceAll("\\s+#", "#").split(AntennaModelBuilder.OPERATORS, 0);

		for (int i = 0; i < splitted.length; ++i) {
			final String linePart = splitted[i];
			if (!linePart.isEmpty() && !containsPreprocessorDirective(linePart, ".*")) {
				setMarkersOnNotExistingOrAbstractFeature(linePart, lineNumber, res);
			}
		}
	}

	/**
	 * Checks whether the text contains the specified directive or not
	 *
	 * @param text text to check
	 * @param directives directives splitted by |
	 * @return true - if the specified directive is contained
	 */
	protected static boolean containsPreprocessorDirective(String text, String directives) {
		return Pattern.compile("//\\s*\\#(" + directives + ")").matcher(text).find();
	}

	@Override
	public ArrayList<String[]> getTemplates() {
		return TEMPLATES;
	}

	private static final ArrayList<String[]> TEMPLATES = createTempltes();

	private static ArrayList<String[]> createTempltes() {
		final ArrayList<String[]> list = new ArrayList<String[]>(1);
		list.add(JAVA_TEMPLATE);
		return list;
	}

	@Override
	public boolean clean() {
		return false;
	}

	@Override
	public boolean createFolderForFeatures() {
		return false;
	}

	@Override
	public boolean hasFeatureFolder() {
		return false;
	}

	@Override
	public boolean hasSourceFolder() {
		return true;
	}

	@Override
	public void copyNotComposedFiles(Configuration config, IFolder destination) {

	}

	@Override
	public void buildFSTModel() {
		antennaModelBuilder.buildModel();
	}

	@Override
	public boolean postAddNature(IFolder source, IFolder destination) {
		return true;
	}

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

	@Override
	public Mechanism getGenerationMechanism() {
		return IComposerExtensionClass.Mechanism.PREPROCESSOR;
	}

	@Override
	public void buildConfiguration(IFolder folder, Configuration configuration, String congurationName) {
		super.buildConfiguration(folder, configuration, congurationName);
		try {
			for (final IResource res : featureProject.getBuildFolder().members()) {
				res.copy(folder.getFile(res.getName()).getFullPath(), true, null);
			}
		} catch (final CoreException e) {
			AntennaCorePlugin.getDefault().logError(e);
		}

		final ArrayList<String> activatedFeatures = new ArrayList<String>();
		for (final IFeature f : configuration.getSelectedFeatures()) {
			activatedFeatures.add(f.getName());
		}
		// generate comma separated string of activated features
		final StringBuilder featureList = new StringBuilder();
		for (final String feature : activatedFeatures) {
			featureList.append(feature + ",");
		}
		final int length = featureList.length();
		if (length > 0) {
			featureList.deleteCharAt(length - 1);
		}

		featureModel = AdvancedNodeCreator.createNodes(configuration.getFeatureModel());

		// add source files
		try {
			// add activated features as definitions to preprocessor
			final Preprocessor preprocessor = new Preprocessor(new AntennaLogger(), new AntennaLineFilter());
			preprocessor.addDefines(featureList.toString());
			// preprocess for all files in source folder
			preprocessSourceFiles(folder, preprocessor, congurationName);
		} catch (CoreException | IOException | PPException e) {
			AntennaCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Customized build for buildConfiguration().
	 */
	private void preprocessSourceFiles(IFolder sourceFolder, Preprocessor preprocessor, String congurationName)
			throws CoreException, FileNotFoundException, IOException {
		for (final IResource res : sourceFolder.members()) {
			if (res instanceof IFolder) {
				// for folders do recursively
				preprocessSourceFiles((IFolder) res, preprocessor, null);
			} else if (res instanceof IFile) {
				if (res.getName().equals(congurationName + "." + getConfigurationExtension())) {
					continue;
				}
				// get all lines from file
				final Vector<String> lines = loadStringsFromFile((IFile) res);

				// do checking and some stuff
				if (featureModel != null) {// TODO check why the FM is null when generating products
					processLinesOfFile(lines, (IFile) res);
				}
				boolean changed = false;
				try {
					// run antenna preprocessor
					changed = preprocessor.preprocess(lines, ((IFile) res).getCharset());

				} catch (final PPException e) {
					featureProject.createBuilderMarker(res, e.getMessage().replace("Line #" + e.getLineNumber() + " :", "Antenna:"), e.getLineNumber() + 1,
							IMarker.SEVERITY_ERROR);
					AntennaCorePlugin.getDefault().logError(e);
				}

				// if preprocessor changed file: save & refresh
				if (changed) {
					FileOutputStream ostr = null;
					try {
						ostr = new FileOutputStream(res.getRawLocation().toOSString());
						Preprocessor.saveStrings(lines, ostr, ((IFile) res).getCharset());
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

	@Override
	public boolean supportsMigration() {
		return false;
	}

	@Override
	public <T extends IComposerObject> T getComposerObjectInstance(Class<T> c) {
		if (c == ADocumentationCommentParser.class) {
			return c.cast(new DocumentationCommentParser());
		}
		return super.getComposerObjectInstance(c);
	}

	/**
	 * Removes annotated lines of preprocessed files.
	 */
	@Override
	public void postProcess(IFolder folder) {
		try {
			for (final IResource res : folder.members()) {
				if (res instanceof IFolder) {
					postProcess((IFolder) res);
				} else if (res instanceof IFile) {
					final String fileExtension = res.getFileExtension();
					if ((fileExtension != null) && fileExtension.equals(getConfigurationExtension())) {
						continue;
					}
					try (final FileInputStream inputStream = new FileInputStream(new File(res.getLocationURI()));
							final BufferedReader reader = new BufferedReader(new InputStreamReader(inputStream, Charset.forName("UTF-8")))) {
						String line = null;
						final StringBuilder content = new StringBuilder();
						boolean hasAnnotations = false;
						while ((line = reader.readLine()) != null) {
							if (!isAnnotation(line)) {
								content.append(line);
								content.append("\r\n");
							} else {
								hasAnnotations = true;
							}
						}
						if (hasAnnotations) {
							setFileContent((IFile) res, content);
						}
					} catch (final IOException e) {
						AntennaCorePlugin.getDefault().logError(e);
					}
				}
			}
		} catch (final CoreException e) {
			AntennaCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Sets the files new content.
	 *
	 * @param file The file
	 * @param content The new content to set
	 */
	private void setFileContent(IFile file, StringBuilder content) {
		final InputStream source = new ByteArrayInputStream(content.toString().getBytes(Charset.availableCharsets().get("UTF-8")));
		try {
			file.setContents(source, false, true, null);
		} catch (final CoreException e) {
			AntennaCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 *
	 */
	// TODO use regex
	private boolean isAnnotation(String line) {
		if (line.matches(".*//\\s*(\\#|\\@).*")) {
			return true;
		}
		return false;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.IComposerExtensionBase#hasPropertyManager()
	 */
	@Override
	public boolean hasPropertyManager() {
		// TODO Auto-generated method stub
		return false;
	}

}
