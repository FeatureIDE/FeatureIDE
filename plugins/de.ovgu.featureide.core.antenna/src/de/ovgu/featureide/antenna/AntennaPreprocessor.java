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
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.LinkedList;
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
import org.prop4j.And;
import org.prop4j.False;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.NodeReader.ErrorHandling;
import org.prop4j.Not;
import org.prop4j.SatSolver;
import org.prop4j.True;
import org.sat4j.specs.TimeoutException;

import antenna.preprocessor.v3.PPException;
import antenna.preprocessor.v3.Preprocessor;
import de.ovgu.featureide.antenna.documentation.DocumentationCommentParser;
import de.ovgu.featureide.antenna.model.AntennaModelBuilder;
import de.ovgu.featureide.antenna.partialproject.CodeBlock;
import de.ovgu.featureide.antenna.partialproject.ElifBlock;
import de.ovgu.featureide.antenna.partialproject.ElseBlock;
import de.ovgu.featureide.antenna.partialproject.IfBlock;
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
		nodereader.setIgnoreMissingFeatures(ErrorHandling.KEEP);
		nodereader.setIgnoreUnparsableSubExpressions(ErrorHandling.KEEP);
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
	public void performFullBuild(Path config) {
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
		expressionStack = new ArrayDeque<>();

		// count of if, ifelse and else to remove after processing of else from stack
		ifelseCountStack = new ArrayDeque<>();

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

				if (!ifelseCountStack.isEmpty() && !containsPreprocessorDirective(line, "else")) {
					ifelseCountStack.push(ifelseCountStack.pop() + 1);
				}

				setMarkersContradictionalFeatures(line, res, j + 1);

				setMarkersNotConcreteFeatures(line, res, j + 1);
			} else if (containsPreprocessorDirective(line, "endif")) {
				while (!ifelseCountStack.isEmpty()) {
					if (ifelseCountStack.peek() == 0) {
						break;
					}

					if (!expressionStack.isEmpty()) {
						expressionStack.pop();
					}

					ifelseCountStack.push(ifelseCountStack.pop() - 1);
				}

				if (!ifelseCountStack.isEmpty()) {
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

		convertLineForNodeReader(line);

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

		// add source files
		try {
			// add activated features as definitions to preprocessor
			final Preprocessor preprocessor = new Preprocessor(new AntennaLogger(), new AntennaLineFilter());
			preprocessor.addDefines(featureList.toString());
			// preprocess for all files in source folder
			preprocessSourceFiles(folder, preprocessor, congurationName, AdvancedNodeCreator.createNodes(featureModel));
		} catch (CoreException | IOException | PPException e) {
			AntennaCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Customized build for buildConfiguration().
	 */
	private void preprocessSourceFiles(IFolder sourceFolder, Preprocessor preprocessor, String congurationName, Node featureModelNode)
			throws CoreException, FileNotFoundException, IOException {
		for (final IResource res : sourceFolder.members()) {
			if (res instanceof IFolder) {
				// for folders do recursively
				preprocessSourceFiles((IFolder) res, preprocessor, null, featureModelNode);
			} else if (res instanceof IFile) {
				if (res.getName().equals(congurationName + "." + getConfigurationFormat().getSuffix())) {
					continue;
				}
				// get all lines from file
				final Vector<String> lines = loadStringsFromFile((IFile) res);

				// do checking and some stuff
				if (featureModelNode != null) {// TODO check why the FM is null when generating products
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
					if ((fileExtension != null) && fileExtension.equals(getConfigurationFormat().getSuffix())) {
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

	@Override
	public void buildPartialFeatureProjectAssets(IFolder sourceFolder, ArrayList<String> removedFeatures, ArrayList<String> coreFeatures)
			throws IOException, CoreException {
		for (final IResource res : sourceFolder.members()) {
			if (res instanceof IFolder) {
				// for folders do recursively
				buildPartialFeatureProjectAssets((IFolder) res, removedFeatures, coreFeatures);
			} else if (res instanceof IFile) {
				// delete all existing builder markers

				featureProject.deleteBuilderMarkers(res, 0);

				// get all lines from file
				final Vector<String> lines = loadStringsFromFile((IFile) res);

				// run antenna preprocessor
				boolean changed = false;
				final CodeBlock codeBlock = new CodeBlock();

				lookForCodeBlocks(codeBlock, 0, lines.size() - 1, lines);
				try {
					changed = updateAnnotations(codeBlock.getChildren(), lines, removedFeatures);
				} catch (final TimeoutException e) {
					e.printStackTrace();
				}

				// if this process changed file: check if the file should be deleted entirely, save & refresh
				if (changed) {
					if (isFileBlank(lines)) {
						res.delete(true, null);
					} else {
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
	}

	private boolean isFileBlank(Vector<String> lines) {
		for (final String line : lines) {
			if (line.trim().length() > 0) {
				return false;
			}
		}
		return true;
	}

	/**
	 * @param children
	 * @param features
	 * @throws TimeoutException
	 */
	private boolean updateAnnotations(ArrayList<CodeBlock> children, Vector<String> lines, ArrayList<String> features) throws TimeoutException {
		final int ANNOTATION_KEPT = 0;
		final int ANNOTATION_REMOVED = 1;
		final int ANNOTATION_AND_BLOCK_REMOVED = 2;

		final ArrayList<Integer> annotationDecision = new ArrayList<Integer>();

		for (int i = 0; i < children.size(); i++) {

			final CodeBlock block = children.get(i);

			final Node beforeNode;
			final Node afterNode;

			beforeNode = block.getNode();
			afterNode = Node.replaceLiterals(beforeNode, features, true);
			// check if anything even needs to be changed for this node
			boolean containsDeletedFeature = false;
			for (final String featureName : beforeNode.getContainedFeatures()) {
				if (features.contains(featureName)) {
					containsDeletedFeature = true;
					break;
				}
			}

			if (!containsDeletedFeature) {
				// node stayed the same
				annotationDecision.add(ANNOTATION_KEPT);
			} else if (!((afterNode instanceof True) || (afterNode instanceof False))) {
				// has a solution and is not a tautology
				// annotation anpassen, dafür afternode zu string verarbeiten

				if (block instanceof ElifBlock) {
					boolean makeIf = false;

					// if all previous blocks have been removed
					for (int x = i - 1; x >= 0; x--) {
						if (children.get(x) instanceof ElifBlock) {
							continue;
						}
						if (children.get(x) instanceof IfBlock) {
							if ((annotationDecision.get(x) == ANNOTATION_AND_BLOCK_REMOVED) || (annotationDecision.get(x) == ANNOTATION_REMOVED)) {
								boolean elifTurnedIf = false;
								for (int y = x + 1; y < i; y++) {
									if (annotationDecision.get(y) == ANNOTATION_KEPT) {
										elifTurnedIf = true;
										break;
									}
								}
								makeIf = !elifTurnedIf;
								break;
							} else {
								makeIf = false;
								break;
							}
						}
					}

					if (makeIf) {
						// Make an if annotation
						lines.set(block.getStartLine(),
								translateNodeToAntennaStatement(Node.replaceLiterals(((ElifBlock) block).getElifNode(), features, true), false));
						annotationDecision.add(ANNOTATION_KEPT);
					} else if (Node.replaceLiterals(((ElifBlock) block).getElifNode(), features, false) instanceof True) {
						// Make an else annotation
						lines.set(block.getStartLine(), "//#else");
						annotationDecision.add(ANNOTATION_KEPT);
					} else {
						// Change elif
						lines.set(block.getStartLine(), translateNodeToAntennaStatement(((ElifBlock) block).getElifNode(), true));
						annotationDecision.add(ANNOTATION_KEPT);
					}
				} else if (block instanceof IfBlock) {
					lines.set(block.getStartLine(), translateNodeToAntennaStatement(afterNode, false));
					annotationDecision.add(ANNOTATION_KEPT);
				} else if (block instanceof ElseBlock) {
					annotationDecision.add(ANNOTATION_KEPT);
				}
			} else if (new SatSolver(beforeNode, 1000).hasSolution() && (afterNode instanceof False)) {
				// removing features causes this annotation to be a contradiction
				// gesamten codeblock entfernen
				for (int line = block.getStartLine(); line <= (block.getEndLine() - 1); line++) {
					lines.set(line, "");
				}
				annotationDecision.add(ANNOTATION_AND_BLOCK_REMOVED);
			} else if (new SatSolver(new Not(beforeNode), 1000).hasSolution() && (afterNode instanceof True)) {
				// removing features causes this annotation to be a tautology
				// annotation entfernen
				lines.set(block.getStartLine(), "");
				annotationDecision.add(ANNOTATION_REMOVED);
			} else if ((!new SatSolver(beforeNode, 1000).hasSolution() && (afterNode instanceof False))
				|| (!new SatSolver(new Not(beforeNode), 1000).hasSolution() && (afterNode instanceof True))) {
				// afterNode is a contradiction or a tautology, but not because of the removal of a feature
				if (block instanceof ElifBlock) {
					if ((Node.replaceLiterals(((ElifBlock) block).getElifNode(), features, false) instanceof False)
						|| (Node.replaceLiterals(((ElifBlock) block).getElifNode(), features, false) instanceof True)) {
						lines.set(block.getStartLine(), "//#else");
						annotationDecision.add(ANNOTATION_KEPT);
					} else {
						if (annotationDecision.get(i - 1) == ANNOTATION_KEPT) {
							lines.set(block.getStartLine(),
									translateNodeToAntennaStatement(Node.replaceLiterals(((ElifBlock) block).getElifNode(), features, false), true));
							annotationDecision.add(ANNOTATION_KEPT);
						} else {
							// make an if
							lines.set(block.getStartLine(),
									translateNodeToAntennaStatement(Node.replaceLiterals(((ElifBlock) block).getElifNode(), features, false), false));
							annotationDecision.add(ANNOTATION_KEPT);
						}
					}
				} else if (block instanceof IfBlock) {
					lines.set(block.getStartLine(), translateNodeToAntennaStatement(Node.replaceLiterals(beforeNode, features, false), false));
					annotationDecision.add(ANNOTATION_KEPT);
				} else if (block instanceof ElseBlock) {
					annotationDecision.add(ANNOTATION_KEPT);
				}
			} else {
				// If there are any other cases, add them here.
			}

			// recursively do the same for children if they haven't already been deleted
			if (annotationDecision.get(i) != ANNOTATION_AND_BLOCK_REMOVED) {
				updateAnnotations(block.getChildren(), lines, features);
			}
		}

		// remove endif for all blocks that are completely gone
		for (int x = 0; x < children.size(); x++) {
			if (children.get(x) instanceof IfBlock) {
				for (int y = x; y < children.size(); y++) {
					if (((y + 1) == children.size()) || (children.get(y + 1) instanceof IfBlock)) {
						boolean removeEndif = true;
						for (int z = x; z <= y; z++) {
							if (annotationDecision.get(z) == ANNOTATION_KEPT) {
								removeEndif = false;
								break;
							}
						}
						if (removeEndif) {
							lines.set(children.get(y).getEndLine(), "");
							break;
						}
					}
				}
			}
		}

		for (final int decision : annotationDecision) {
			if (decision != ANNOTATION_KEPT) {
				return true;
			}
		}

		return false;
	}

	/**
	 * @param afterNode
	 * @return
	 */
	private String translateNodeToAntennaStatement(Node node, boolean elif) {
		final String line;

		if (elif) {
			line = "//#elif ";
		} else {
			line = "//#if ";
		}
		String statement = node.toString();

		statement = statement.replace("&", " && ");
		statement = statement.replace("|", " || ");
		statement = statement.replace("-", "!");
		return line + statement;
	}

	/**
	 * @param codeBlocks
	 * @param i
	 * @param size
	 */
	private void lookForCodeBlocks(CodeBlock parentBlock, int firstLine, int lastLine, Vector<String> lines) {
		CodeBlock block = null;
		int ifcount = 0;
		for (int currentLine = firstLine; currentLine <= lastLine; currentLine++) {
			final String line = lines.get(currentLine);
			// if line is preprocessor directive
			if (containsPreprocessorDirective(line, "ifdef|ifndef|condition|elifdef|elifndef|if|else|elif")) {
				if (containsPreprocessorDirective(line, "ifdef|ifndef|condition|if")) {
					if (block == null) {
						block = new IfBlock(currentLine, nodereader.stringToNode(convertLineForNodeReader(line)));
					} else {
						ifcount++;
					}
				} else if (containsPreprocessorDirective(line, "elifdef|elifndef|else|elif")) {
					if (block == null) {
						if (containsPreprocessorDirective(line, "else")) {
							// This is never supposed to happen, invalid input
							block = new ElseBlock(currentLine, null);
						} else if (containsPreprocessorDirective(line, "elif")) {
							block = new ElifBlock(currentLine, null, null);
						}
					} else if ((ifcount == 0) && (block != null)) {
						if (containsPreprocessorDirective(line, "else")) {
							block.setEndLine(currentLine);
							parentBlock.addChild(block);

							final Node buildNode = getPreviousNodesNegated(parentBlock);

							block = new ElseBlock(currentLine, buildNode);
						} else if (containsPreprocessorDirective(line, "elif")) {
							block.setEndLine(currentLine);
							parentBlock.addChild(block);

							final Node buildNode = getPreviousNodesNegated(parentBlock);
							final Node elifNode = nodereader.stringToNode(convertLineForNodeReader(line));

							block = new ElifBlock(currentLine, new And(buildNode, elifNode), elifNode);
						}
					}
				}
			} else if (containsPreprocessorDirective(line, "endif")) {
				if ((ifcount == 0) && (block != null)) {
					block.setEndLine(currentLine);
					lookForCodeBlocks(block, block.getStartLine() + 1, currentLine - 1, lines);
					parentBlock.addChild(block);
					block = null;
				} else {
					ifcount--;
				}
			}
		}
	}

	/**
	 * @param parentBlock
	 * @param buildNode
	 * @return
	 */
	private Node getPreviousNodesNegated(CodeBlock parentBlock) {
		Node buildNode = null;
		for (int i = parentBlock.getChildren().size() - 1; i >= 0; i--) {
			final CodeBlock currentBlock = parentBlock.getChildren().get(i);
			if (buildNode == null) {
				if (currentBlock instanceof IfBlock) {
					buildNode = new Not(currentBlock.getNode());
					break;
				} else if (currentBlock instanceof ElifBlock) {
					buildNode = new Not(((ElifBlock) currentBlock).getElifNode());
					continue;
				}
			} else {
				if (currentBlock instanceof IfBlock) {
					buildNode = new And(buildNode, new Not(currentBlock.getNode()));
					break;
				} else if (currentBlock instanceof ElifBlock) {
					buildNode = new And(buildNode, new Not(((ElifBlock) currentBlock).getElifNode()));
					continue;
				}
			}
		}
		return buildNode;
	}

	@Override
	public boolean supportsPartialFeatureProject() {
		return true;
	}

	private String convertLineForNodeReader(String line) {
		String trimmedLine = line;

		// remove "//#if ", "//ifdef", ...
		trimmedLine = replaceCommandPattern.matcher(trimmedLine).replaceAll("");

		trimmedLine = trimmedLine.trim();
		trimmedLine = trimmedLine.replace("&&", "&");
		trimmedLine = trimmedLine.replace("||", "|");
		trimmedLine = trimmedLine.replace("!", "-");
		trimmedLine = trimmedLine.replace("==", "=");

		trimmedLine = trimmedLine.replace("&", " and ");
		trimmedLine = trimmedLine.replace("|", " or ");
		trimmedLine = trimmedLine.replace("-", " not ");

		trimmedLine = trimmedLine.replace("=", " iff ");
		return trimmedLine;
	}
}
