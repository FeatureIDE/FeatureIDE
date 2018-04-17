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
package de.ovgu.featureide.featurehouse;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.UnsupportedEncodingException;
import java.nio.charset.Charset;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Locale;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.jdt.core.IClasspathAttribute;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.core.ClasspathEntry;
import org.eclipse.jdt.internal.core.JavaProject;
import org.eclipse.jface.dialogs.MessageDialog;
import org.prop4j.Node;
import org.prop4j.NodeWriter;
import org.sat4j.specs.TimeoutException;

import AST.Problem;
import AST.Program;
import cide.gparser.ParseException;
import cide.gparser.TokenMgrError;
import composer.CmdLineInterpreter;
import composer.CompositionException;
import composer.FSTGenComposer;
import composer.FSTGenComposerExtension;
import composer.ICompositionErrorListener;
import composer.IParseErrorListener;
import composer.rules.meta.FeatureModelInfo;
import de.ovgu.cide.fstgen.ast.FSTNode;
import de.ovgu.cide.fstgen.ast.FSTTerminal;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.core.builder.IComposerObject;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.signature.documentation.base.ADocumentationCommentParser;
import de.ovgu.featureide.featurehouse.errorpropagation.ErrorPropagation;
import de.ovgu.featureide.featurehouse.meta.FeatureIDEModelInfo;
import de.ovgu.featureide.featurehouse.meta.featuremodel.FeatureModelClassGenerator;
import de.ovgu.featureide.featurehouse.model.FeatureHouseModelBuilder;
import de.ovgu.featureide.featurehouse.signature.documentation.DocumentationCommentParser;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.job.IJob;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import fuji.CompilerWarningException;
import fuji.CompositionErrorException;
import fuji.FeatureDirNotFoundException;
import fuji.Main;
import fuji.SemanticErrorException;
import fuji.SyntacticErrorException;

/**
 * Composes files using FeatureHouse.
 *
 * @author Tom Brosch
 * @author Jens Meinicke
 */
// TODO set "Composition errors" like *.png could not be composed with *.png
@SuppressWarnings("restriction")
public class FeatureHouseComposer extends ComposerExtensionClass {

	private static final QualifiedName BUILD_META_PRODUCT =
		new QualifiedName(FeatureHouseComposer.class.getName() + "#BuildMetaProduct", FeatureHouseComposer.class.getName() + "#BuildMetaProduct");
	private static final QualifiedName USE_FUJI =
		new QualifiedName(FeatureHouseComposer.class.getName() + "#Fuji", FeatureHouseComposer.class.getName() + "#Fuji");
	private static final String TRUE = "true";
	private static final String FALSE = "false";

	private static final String FINAL_METHOD = "\\final_method";
	private static final String ORIGINAL = "\\original";
	private static final String FINAL_CONTRACT = "\\final_contract";
	private static final FeatureHouseCorePlugin LOGGER = FeatureHouseCorePlugin.getDefault();
	private static final String CONTRACT_COMPOSITION_CONSECUTIVE_CONTRACT_REFINEMENT = "consecutive contract refinement";
	private static final String CONTRACT_COMPOSITION_EXPLICIT_CONTRACT_REFINEMENT = "explicit contract refinement";
	private static final String CONTRACT_COMPOSITION_CONTRACT_OVERRIDING = "contract overriding";
	private static final String CONTRACT_COMPOSITION_PLAIN_CONTRACTING = "plain contracting";
	private static final String CONTRACT_COMPOSITION_PLAIN_CONTRACT = "plain_contracting";
	private static final String CONTRACT_COMPOSITION_EXPLICIT_CONTRACTING = "explicit_contracting";
	private static final String CONTRACT_COMPOSITION_CONSECUTIVE_CONTRACTING = "consecutive_contracting";
	private static final String CONTRACT_COMPOSITION_CUMULATIVE_CONTRACT_REFINEMENT = "cumulative contract refinement";
	private static final String CONTRACT_COMPOSITION_CUMULATIVE_CONTRACTING = "cumulative_contracting";
	private static final String CONTRACT_COMPOSITION_CONJUNCTIVE_CONTRACT_REFINEMENT = "conjunctive contract refinement";
	private static final String CONTRACT_COMPOSITION_CONJUNCTIVE_CONTRACTING = "conjunctive_contracting";
	private static final String CONTRACT_COMPOSITION_METHOD_BASED_COMPOSITION = "method-based composition";
	private static final String CONTRACT_COMPOSITION_METHOD_BASED = "method_based";
	private static final String CONTRACT_COMPOSITION_NONE = "none";

	private enum CompKeys {
		conjunctive_contract, consecutive_contract, cumulative_contract, final_contract, final_method
	}

	public static final String COMPOSER_ID = "de.ovgu.featureide.composer.featurehouse";

	private FSTGenComposer composer;

	public FeatureHouseModelBuilder fhModelBuilder;

	private ErrorPropagation errorPropagation = null;

	private final IParseErrorListener listener = createParseErrorListener();

	private IParseErrorListener createParseErrorListener() {
		return new IParseErrorListener() {

			@Override
			public void parseErrorOccured(ParseException e) {
				createBuilderProblemMarker(e.currentToken.next.endLine, e.getMessage());
			}
		};
	}

	private final ICompositionErrorListener compositionErrorListener = createCompositionErrorListener();
	private IJob<?> fuji;

	private ICompositionErrorListener createCompositionErrorListener() {
		return new ICompositionErrorListener() {

			@Override
			public void parseErrorOccured(CompositionException e) {
				FSTTerminal terminal = e.getTerminalB();

				if (e.getMessage().contains(ORIGINAL)) {
					if (!e.getTerminalB().getBody().contains(ORIGINAL)) {
						terminal = e.getTerminalA();
					}
				}

				IFile file = null;
				int lineFile = -1;
				if (terminal != null) {
					file = getFile(terminal);
					lineFile = terminal.beginLine;

					if (file != null) {
						try {
							final IMarker marker = file.createMarker(FeatureHouseCorePlugin.BUILDER_PROBLEM_MARKER);
							marker.setAttribute(IMarker.LINE_NUMBER, lineFile);
							marker.setAttribute(IMarker.MESSAGE, e.getMessage());
							marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_WARNING);
						} catch (final CoreException e2) {
							LOGGER.logError(e2);
						}
					} else {
						LOGGER.logError(new Exception("No file provided for: " + terminal.toString()));
					}
				}
			}

			private IFile getFile(FSTTerminal terminal) {
				if (terminal == null) {
					return null;
				}
				FSTNode fileNode = terminal.getParent();
				while ((fileNode != null) && !fileNode.getName().endsWith(".java")) {
					fileNode = fileNode.getParent();
				}
				if (fileNode != null) {
					final FSTNode featureNode = fileNode.getParent();
					return featureProject.getSourceFolder().getFolder(featureNode.getName()).getFile(fileNode.getName());
				} else {
					LOGGER.logError(new Exception("Java file could not be found for: " + terminal.toString()));
					return null;
				}
			}
		};
	}

	@Override
	public boolean initialize(IFeatureProject project) {
		final boolean supSuccess = super.initialize(project);
		fhModelBuilder = new FeatureHouseModelBuilder(project);
		createBuildStructure();
		checkJavaBuildPath();
		return supSuccess && (fhModelBuilder != null);
	}

	/**
	 * Creates an error marker to the last error file.
	 *
	 * @param line The line of the marker.
	 * @param message The message.
	 */
	protected void createBuilderProblemMarker(int line, String message) {
		message = detruncateString(message);
		try {
			final IMarker marker = getErrorFile().createMarker(FeatureHouseCorePlugin.BUILDER_PROBLEM_MARKER);
			marker.setAttribute(IMarker.LINE_NUMBER, line);
			marker.setAttribute(IMarker.MESSAGE, message);
			marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
		} catch (final CoreException e) {
			LOGGER.logError(e);
		}

	}

	/**
	 * @param message The message
	 * @return A substring of message that is smaller than 65535 bytes.
	 */
	private static String detruncateString(String message) {
		byte[] bytes;
		try {
			bytes = message.getBytes(("UTF-8"));
			if (bytes.length > 65535) {
				message = message.substring(0, 65535 / 2);
			}

		} catch (final UnsupportedEncodingException e) {
			LOGGER.logError(e);
		}
		return message;
	}

	/**
	 * Gets the file containing the actual error.
	 *
	 * @return The file.
	 */
	protected IFile getErrorFile() {
		return featureProject.getProject().getWorkspace().getRoot().findFilesForLocationURI(composer.getErrorFiles().getLast().toURI())[0];
	}

	/**
	 * Removes line and column form the message of the TokenMgrError.<br> Example message:<br> -Lexical error at line 7, column 7. Encountered: <EOF> after : ""
	 *
	 * @param message The message
	 * @return message without "line i, column j."
	 */
	private String getTokenMgrErrorMessage(String message) {
		if (!message.contains("line ") || !message.contains("Encountered")) {
			return message;
		}
		return message.substring(0, message.indexOf(" at ")) + " e" + message.substring(message.indexOf("ncountered:"));
	}

	/**
	 * Gets the line of the message of the TokenMgrError.<br> Example message:<br> -Lexical error at line 7, column 7. Encountered: <EOF> after : ""
	 *
	 * @param message The error message
	 * @return The line
	 */
	private int getTokenMgrErrorLine(String message) {
		if (!message.contains("line ")) {
			return -1;
		}
		return Integer.parseInt(message.substring(message.indexOf("line ") + 5, message.indexOf(',')));
	}

	/**
	 * Checks the current folder structure at the build folder and creates folders if necessary.
	 */
	private void createBuildStructure() {
		final IProject p = featureProject.getProject();
		if (p != null) {
			final IFolder sourcefolder = featureProject.getBuildFolder();
			if (sourcefolder != null) {
				if (!sourcefolder.exists()) {
					try {
						sourcefolder.create(true, true, null);
					} catch (final CoreException e) {
						LOGGER.logError(e);
					}
				}
			}
		}
	}

	/**
	 * Checks whether the java build path is equal to the defined build path of the FeatureIDE project.<br> Only necessary for FeatureHouse projects with the
	 * old build structure.
	 */
	private void checkJavaBuildPath() {
		try {
			final JavaProject javaProject = new JavaProject(featureProject.getProject(), null);
			final IClasspathEntry[] classpathEntrys = javaProject.getRawClasspath();

			int index = 0;
			for (final IClasspathEntry e : classpathEntrys) {
				if (e.getEntryKind() == IClasspathEntry.CPE_SOURCE) {
					final IPath path = featureProject.getBuildFolder().getFullPath();

					/** return if nothing has to be changed **/
					if (e.getPath().equals(path)) {
						return;
					}

					if (!path.isPrefixOf(e.getPath())) {
						continue;
					}

					/** change the actual source entry to the new build path **/
					final ClasspathEntry changedEntry = new ClasspathEntry(e.getContentKind(), e.getEntryKind(), path, e.getInclusionPatterns(),
							e.getExclusionPatterns(), e.getSourceAttachmentPath(), e.getSourceAttachmentRootPath(), null, e.isExported(), e.getAccessRules(),
							e.combineAccessRules(), e.getExtraAttributes());
					classpathEntrys[index] = changedEntry;
					javaProject.setRawClasspath(classpathEntrys, null);
					return;
				}
				index++;
			}

			/**
			 * case: there is no source entry at the class path add the source entry to the classpath
			 **/
			final IFolder folder = featureProject.getBuildFolder();
			final ClasspathEntry sourceEntry = new ClasspathEntry(IPackageFragmentRoot.K_SOURCE, IClasspathEntry.CPE_SOURCE, folder.getFullPath(), new IPath[0],
					new IPath[0], null, null, null, false, null, false, new IClasspathAttribute[0]);
			final IClasspathEntry[] newEntrys = new IClasspathEntry[classpathEntrys.length + 1];
			System.arraycopy(classpathEntrys, 0, newEntrys, 0, classpathEntrys.length);
			newEntrys[newEntrys.length - 1] = sourceEntry;
			javaProject.setRawClasspath(newEntrys, null);
		} catch (final JavaModelException e) {
			LOGGER.logError(e);
		}
	}

	@Override
	public void performFullBuild(IFile config) {
		assert (featureProject != null) : "Invalid project given";

		final Path temporaryConfigrationFile = createTemporaryConfigrationFile(config);
		if (temporaryConfigrationFile == null) {
			return;
		}
		final String configPath = temporaryConfigrationFile.toString();

		final String basePath = featureProject.getSourcePath();
		final String outputPath = featureProject.getBuildPath();
		if ((basePath == null) || (outputPath == null)) {
			return;
		}

		final SignatureSetter signatureSetter = new SignatureSetter();

		/*
		 * Run fuji parallel to the build process.
		 */
		fuji(signatureSetter);

		if (buildMetaProduct()) {
			if (IFeatureProject.META_MODEL_CHECKING_BDD_JAVA_JML.equals(featureProject.getMetaProductGeneration())) {
				buildDefaultMetaProduct(configPath, basePath, outputPath);
			} else if (IFeatureProject.META_MODEL_CHECKING_BDD_JAVA.equals(featureProject.getMetaProductGeneration())) {
				buildBDDMetaProduct(configPath, basePath, outputPath, "java");
			} else if (IFeatureProject.META_VAREXJ.equals(featureProject.getMetaProductGeneration())) {
				buildDefaultMetaProduct(configPath, basePath, outputPath);
			} else if (IFeatureProject.META_MODEL_CHECKING_BDD_C.equals(featureProject.getMetaProductGeneration())) {
				buildBDDMetaProduct(configPath, basePath, outputPath, "c");
			} else {
				buildDefaultMetaProduct(configPath, basePath, outputPath);
			}
		} else {
			composer = new FSTGenComposer(false);
			composer.addCompositionErrorListener(compositionErrorListener);
			try {
				composer.run(getArguments(configPath, basePath, outputPath, getContractParameter()));
			} catch (final TokenMgrError e) {

			}
		}
		buildFSTModel(configPath, basePath, outputPath);
		signatureSetter.setFstModel(featureProject.getFSTModel());

		checkContractComposition();
	}

	private void checkContractComposition() {
		try {
			deleteContractErrorMarkers();

			final FSTModel fstModel = featureProject.getFSTModel();
			if (fstModel == null) {
				return;
			}

			final String contractParameter = getContractParameter();
			if (!contractParameter.equals(CONTRACT_COMPOSITION_EXPLICIT_CONTRACTING)) {
				for (final FSTClass c : fstModel.getClasses()) {
					for (final FSTRole r : c.getRoles()) {
						for (final FSTMethod m : r.getClassFragment().getMethods()) {
							if (m.hasContract() && m.getContract().contains("original")) {
								if (m.getCompKey().isEmpty() && contractParameter.equals(CONTRACT_COMPOSITION_METHOD_BASED)) {
									continue;
								}
								setContractErrorMarker(m, "Keyword original ignored. Contract composition set to " + contractParameter
									+ ". Change to \"Explicit Contract Refinement\".");
							}
						}
					}
				}
			}

			if (!contractParameter.equals(CONTRACT_COMPOSITION_METHOD_BASED)) {
				for (final FSTClass c : fstModel.getClasses()) {
					for (final FSTRole r : c.getRoles()) {
						for (final FSTMethod m : r.getClassFragment().getMethods()) {
							if (m.getCompKey().length() > 0) {
								setContractErrorMarker(m, ": Keyword " + m.getCompKey() + " ignored. Contract composition set to " + contractParameter
									+ ". Change to \"method-based composition\".");
							}
						}
					}
				}

			} else {
				final IFeatureModel featureModel = featureProject.getFeatureModel();
				final IFeatureModelFactory factory = FMFactoryManager.getFactory(featureModel);
				for (final FSTClass c : fstModel.getClasses()) {
					for (final FSTRole r : c.getRoles()) {
						final IFeature featureRole1 = featureModel.getFeature(r.getFeature().getName());
						for (final FSTMethod m : r.getClassFragment().getMethods()) {
							final List<IFeature> currentFeatureList = new LinkedList<IFeature>();
							final List<IFeature> originalList = new LinkedList<IFeature>();

							currentFeatureList.add(factory.createFeature(featureModel, r.getFeature().getName()));

							for (final String feat : featureModel.getFeatureOrderList()) {
								if (feat.equals(r.getFeature().getName())) {
									break;
								}
								final FSTRole rr = c.getRole(feat);
								if (rr == null) {
									continue;
								}
								final IFeature featureRole2 = featureModel.getFeature(feat);
								for (final FSTMethod mm : rr.getClassFragment().getMethods()) {

									if (checkForOriginalInContract(m, mm)) {
										originalList.add(featureRole2);
									}

									if (checkForIllegitimateMethodRefinement(m, mm)) {
										final List<IFeature> finalMethodList = new LinkedList<IFeature>();
										finalMethodList.add(featureRole2);
										if (!featureModel.getAnalyser().checkIfFeatureCombinationNotPossible(featureRole1, finalMethodList)) {
											setContractErrorMarker(m, "keyword \"\\final_method\" found but possibly later refinement.");
										}
									}

									if (checkForIllegitimateContract(m, mm)) {
										final List<IFeature> finalContractList = new LinkedList<IFeature>();
										finalContractList.add(featureRole2);
										if (mm.getCompKey().contains(FINAL_CONTRACT) && !featureModel.getAnalyser().checkIfFeatureCombinationNotPossible(
												factory.createFeature(featureModel, r.getFeature().getName()), finalContractList)) {
											setContractErrorMarker(m, "keyword \"\\final_contract\" found but possibly later contract refinement.");
										}
									}

									if (checkForIllegitimaterefinement(m, mm)) {
										final LinkedList<IFeature> treeDependencyList = new LinkedList<IFeature>();
										treeDependencyList.add(featureRole2);
										if (!featureModel.getAnalyser().checkIfFeatureCombinationNotPossible(featureRole1, treeDependencyList)) {
											setContractErrorMarker(m, "Contract with composition keyword " + mm.getCompKey()
												+ " possibily illegitimately redefined with keyword " + m.getCompKey() + ".");
										}
									}

								}
							}
							if (m.getContract().contains(ORIGINAL)
								&& !(!originalList.isEmpty() ? featureModel.getAnalyser().checkImplies(currentFeatureList, originalList) : false)) {
								setContractErrorMarker(m, "keyword \"\\original\" found but no mandatory previous introduction.");
							}
						}
					}
				}
			}
		} catch (final CoreException e2) {
			LOGGER.logError(e2);
		} catch (final TimeoutException e) {
			LOGGER.logError(e);
		}

	}

	/**
	 * Check if there is an introductionary method contract for methods that contain the keyword original in contract.
	 */
	private boolean checkForOriginalInContract(FSTMethod m, FSTMethod mm) {
		return m.hasContract() && m.getContract().contains(ORIGINAL) && mm.getName().equals(m.getName()) && mm.hasContract();
	}

	/**
	 * Check if a method whose contract is marked with \final_method is redefine.
	 *
	 *
	 * @param m
	 * @param mm
	 * @return
	 */
	private boolean checkForIllegitimateMethodRefinement(FSTMethod m, FSTMethod mm) {
		return mm.getCompKey().contains(FINAL_METHOD) && mm.getFullName().equals(m.getFullName());
	}

	/**
	 * Check if a method whose contract is marked with \final_contract is redefined.
	 *
	 * @param m
	 * @param mm
	 * @return
	 */
	private boolean checkForIllegitimateContract(FSTMethod m, FSTMethod mm) {
		return m.hasContract() && mm.getCompKey().contains(FINAL_CONTRACT) && mm.getFullName().equals(m.getFullName()) && mm.hasContract();
	}

	/**
	 * Check if a method contract's composition technique is illegitimately redefined with another technique.
	 *
	 * @param m
	 * @param mm
	 * @return
	 */
	private boolean checkForIllegitimaterefinement(FSTMethod m, FSTMethod mm) {
		return m.hasContract() && (m.getCompKey().length() > 0) && (mm.getCompKey().length() > 0)
			&& (CompKeys.valueOf(m.getCompKey().substring(1)).ordinal() > 0) && mm.getFullName().equals(m.getFullName())
			&& (CompKeys.valueOf(mm.getCompKey().substring(1)).ordinal() > CompKeys.valueOf(m.getCompKey().substring(1)).ordinal());
	}

	/**
	 * @throws CoreException
	 */
	private void deleteContractErrorMarkers() throws CoreException {
		final IFolder sourceFolder = featureProject.getComposer().hasFeatureFolder() ? featureProject.getSourceFolder() : featureProject.getBuildFolder();
		final IMarker[] markers = sourceFolder.findMarkers(FeatureHouseCorePlugin.CONTRACT_MARKER, false, IResource.DEPTH_INFINITE);
		for (final IMarker marker : markers) {
			marker.delete();
		}
	}

	/**
	 * @param m
	 * @throws CoreException
	 */
	private void setContractErrorMarker(FSTMethod m, String message) throws CoreException {
		final IMarker marker = m.getFile().createMarker(FeatureHouseCorePlugin.CONTRACT_MARKER);
		marker.setAttribute(IMarker.LINE_NUMBER, m.getLine());
		marker.setAttribute(IMarker.MESSAGE, m.getName() + ": " + message);
		marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_WARNING);
	}

	/**
	 * @param configPath
	 * @param basePath
	 * @param outputPath
	 */
	private void buildDefaultMetaProduct(final String configPath, final String basePath, final String outputPath) {
		new FeatureModelClassGenerator(featureProject);
		FSTGenComposerExtension.key = IFeatureProject.META_THEOREM_PROVING.equals(featureProject.getMetaProductGeneration())
			|| IFeatureProject.META_MODEL_CHECKING_BDD_JAVA_JML.equals(featureProject.getMetaProductGeneration())
			|| IFeatureProject.META_VAREXJ.equals(featureProject.getMetaProductGeneration());
		final FSTGenComposerExtension composerExtension = new FSTGenComposerExtension();
		composer = composerExtension;
		composerExtension.addCompositionErrorListener(compositionErrorListener);
		final IFeatureModel featureModel = featureProject.getFeatureModel();
		final Collection<String> featureOrderList = featureModel.getFeatureOrderList();
		// dead features should not be composed
		final LinkedList<String> deadFeatures = new LinkedList<String>();
		for (final IFeature deadFeature : featureModel.getAnalyser().getDeadFeatures()) {
			deadFeatures.add(deadFeature.getName());
		}

		final String[] features = new String[featureOrderList.size()];
		int i = 0;
		for (final String f : featureOrderList) {
			if (!deadFeatures.contains(f)) {
				features[i++] = f;
			}
		}

		try {
			final String[] args = getArguments(configPath, basePath, outputPath, getContractParameter());
			final FeatureModelInfo modelInfo =
				new FeatureIDEModelInfo(featureModel, !IFeatureProject.META_THEOREM_PROVING.equals(featureProject.getMetaProductGeneration()));
			composerExtension.setModelInfo(modelInfo);
			composerExtension.buildMetaProduct(args, features);
		} catch (final TokenMgrError e) {} catch (final Error e) {
			LOGGER.logError(e);
		}
	}

	private static String SPLModelChecker = "package verificationClasses;\r\n" + "import gov.nasa.jpf.jvm.Verify;\r\n" + "public class SPLModelChecker {\r\n"
		+ "\tpublic static boolean getBoolean() {\r\n" + "\t\treturn Verify.getBoolean(false);\r\n" + "\t}\r\n\r\n"
		+ "\tpublic static int getIntMinMax(int min, int max) {\r\n" + "\t\treturn Verify.getInt(min, max);\r\n" + "\t}\r\n" + "}";

	/**
	 * @param configPath
	 * @param basePath
	 * @param outputPath
	 * @param language
	 */
	@SuppressWarnings("deprecation")
	private void buildBDDMetaProduct(final String configPath, final String basePath, final String outputPath, String language) {
		composer = new FSTGenComposerExtension();
		composer.addCompositionErrorListener(compositionErrorListener);
		try {
			final IFile cnfFile = featureProject.getSourceFolder().getFile("model.cnf");
			final Node nodes = AdvancedNodeCreator.createCNF(featureProject.getFeatureModel());
			String input = nodes.toString(NodeWriter.javaSymbols);
			input = input.replaceAll("!", "! ");
			final InputStream cnfSource = new ByteArrayInputStream(input.getBytes(Charset.availableCharsets().get("UTF-8")));
			try {
				if (cnfFile.exists()) {
					cnfFile.setContents(cnfSource, false, true, null);
				} else {
					cnfFile.create(cnfSource, true, null);
				}
				cnfFile.setDerived(true);
			} catch (final CoreException e) {
				LOGGER.logError(e);
			}

			final String[] arguments = getArguments(configPath, basePath, outputPath, getContractParameter());
			final String[] newArgs = new String[arguments.length + 1];
			int i = 0;
			for (final String arg : arguments) {
				newArgs[i++] = arg;
			}
			newArgs[i] = CmdLineInterpreter.INPUT_OPTION_LIFTING + language;
			composer.run(newArgs);

			final IFolder verificationClasses =
				featureProject.getBuildFolder().getFolder(featureProject.getCurrentConfiguration().getName().split("[.]")[0]).getFolder("verificationClasses");
			verificationClasses.create(true, true, null);
			featureProject.getBuildFolder().refreshLocal(IResource.DEPTH_ONE, null);
			for (final IResource res : featureProject.getBuildFolder().members()) {
				if (res.getName().equals("FeatureSwitches.java")) {
					res.move(verificationClasses.getFile("FeatureSwitches.java").getFullPath(), true, null);
				}
			}

			final IFile sPLModelCheckerFile = verificationClasses.getFile("SPLModelChecker.java");
			final InputStream source = new ByteArrayInputStream(SPLModelChecker.getBytes(Charset.availableCharsets().get("UTF-8")));
			try {
				if (sPLModelCheckerFile.exists()) {
					sPLModelCheckerFile.setContents(source, false, true, null);
				} else {
					sPLModelCheckerFile.create(source, true, null);
				}
				sPLModelCheckerFile.setDerived(true);
			} catch (final CoreException e) {
				LOGGER.logError(e);
			}

		} catch (final TokenMgrError e) {

		} catch (final CoreException e) {
			LOGGER.logError(e);
		}
	}

	/**
	 * Starts type checking with fuji in a background job.
	 */
	private void fuji(final SignatureSetter signatureSetter) {
		if (!usesFuji()) {
			return;
		}
		if (fuji != null) {
			fuji.cancel();
			try {
				fuji.join();
			} catch (final InterruptedException e) {
				FMCorePlugin.getDefault().logError(e);
			}
		}
		final LongRunningMethod<Boolean> job = new LongRunningMethod<Boolean>() {

			@Override
			public Boolean execute(IMonitor workMonitor) throws Exception {
				try {
					final Program ast = runFuji(featureProject);
					signatureSetter.setFujiParameters(featureProject, ast);
					return true;
				} catch (final CompositionException e) {
					FMCorePlugin.getDefault().logError(e);
					return false;
				}
			}
		};
		fuji = LongRunningWrapper.getRunner(job, "Type checking " + featureProject.getProjectName() + " with fuji");
		fuji.schedule();
	}

	/**
	 * Runs the type checker fuji. synchronized because fuji use static fields, and a parallel execution is not possible.
	 *
	 * @param featureProject The feature project of the caller.
	 */
	private synchronized static Program runFuji(IFeatureProject featureProject) throws CompositionException {
		final String sourcePath = featureProject.getSourcePath();
		final String[] fujiOptions = new String[] { "-" + Main.OptionName.CLASSPATH, getClassPaths(featureProject), "-" + Main.OptionName.PROG_MODE,
			"-" + Main.OptionName.COMPOSTION_STRATEGY, Main.OptionName.COMPOSTION_STRATEGY_ARG_FAMILY, "-typechecker", "-basedir", sourcePath };
		Program ast = null;
		try {
			final IFeatureModel fm = featureProject.getFeatureModel();
			fm.getAnalyser().setDependencies();

			final Main fuji = new Main(fujiOptions, fm, null);

			ast = fuji.getComposition(fuji).composeAST();
			ast.setCmd(fuji.getCmd());

			// run type check
			fuji.typecheckAST(ast);

			// parsing warnings
			for (final Problem warn : fuji.getWarnings()) {
				createFujiMarker(warn.line(), warn.message(), warn.fileName(), IMarker.SEVERITY_WARNING, featureProject);
			}

			// parsing errors
			for (final Problem err : fuji.getErrors()) {
				final String message = err.message();
				if (err.line() == -1) {
					for (final String fileName : err.fileName().split("[\n]")) {
						// currently bad workaround @ fuji, but seems to work
						final String file = fileName.substring(0, fileName.lastIndexOf(":"));
						final int line = Integer.parseInt(fileName.substring(fileName.lastIndexOf(":") + 1));
						createFujiMarker(line, message, file, IMarker.SEVERITY_ERROR, featureProject);
					}
				} else {
					createFujiMarker(err.line(), message, err.fileName(), IMarker.SEVERITY_ERROR, featureProject);
				}

			}
		} catch (final CompositionErrorException e) {
			createFujiMarker(-1, e.getMessage(), featureProject.getSourceFolder(), IMarker.SEVERITY_ERROR, featureProject);
		} catch (
				IllegalArgumentException | org.apache.commons.cli.ParseException | IOException | FeatureDirNotFoundException | SyntacticErrorException
				| SemanticErrorException | CompilerWarningException | UnsupportedModelException e) {
			LOGGER.logError(e);
		}

		return ast;
	}

	public static String getClassPaths(IFeatureProject featureProject) {
		final StringBuilder classpath = new StringBuilder();
		final String sep = System.getProperty("path.separator");
		try {
			final JavaProject proj = new JavaProject(featureProject.getProject(), null);
			final IJavaElement[] elements = proj.getChildren();
			for (final IJavaElement e : elements) {
				final String path = e.getPath().toOSString();
				if (path.contains(":")) {
					classpath.append(sep);
					classpath.append(path);
					continue;
				}
				final IResource resource = e.getResource();
				if ((resource != null) && "jar".equals(resource.getFileExtension())) {
					classpath.append(sep);
					classpath.append(resource.getRawLocation().toOSString());
				}
			}
		} catch (final JavaModelException e) {

		}
		return classpath.length() > 0 ? classpath.substring(1) : classpath.toString();
	}

	/**
	 * Creates an marker for fuji type checks.
	 *
	 * @param line The line number
	 * @param message The message to display
	 * @param file The file path
	 * @param severity The severity of the marker (IMarker.SEVERITY_*)
	 */
	protected static void createFujiMarker(int line, String message, String file, int severity, IFeatureProject featureProject) {
		final IFile iFile = featureProject.getProject().getWorkspace().getRoot().findFilesForLocationURI(new File(file).toURI())[0];
		createFujiMarker(line, message, iFile, severity, featureProject);
	}

	/**
	 * Creates an marker for fuji type checks.
	 *
	 * @param line The line number
	 * @param message The message to display
	 * @param file The file
	 * @param severity The severity of the marker (IMarker.SEVERITY_*)
	 */
	private static void createFujiMarker(int line, String message, IResource file, int severity, IFeatureProject featureProject) {
		// TODO NEWLine does not work
		message = message.replace("\n", NEWLINE);
		try {
			final IMarker marker = file.createMarker(FeatureHouseCorePlugin.BUILDER_PROBLEM_MARKER);
			marker.setAttribute(IMarker.LINE_NUMBER, line);
			marker.setAttribute(IMarker.MESSAGE, "fuji: " + message);
			marker.setAttribute(IMarker.SEVERITY, severity);
		} catch (final CoreException e) {
			LOGGER.logError(e);
		}

	}

	/**
	 * Builds the fst model.
	 *
	 * @param configPath
	 * @param basePath
	 * @param outputPath
	 */
	private void buildFSTModel(final String configPath, final String basePath, final String outputPath) {
		// build the fst model of the current product
		/**
		 * It is necessary to also build the model of the current product, because the line numbers of generated elements (e.g., methods) are necessary for
		 * error propagation.
		 **/
		fhModelBuilder.buildModel(composer.getFstnodes(), false);

		// build the complete fst model
		final FSTGenComposerExtension composerExtension = new FSTGenComposerExtension();
		composer = composerExtension;
		composerExtension.addParseErrorListener(listener);
		final List<String> featureOrder = featureProject.getFeatureModel().getFeatureOrderList();
		final String[] features = new String[featureOrder.size()];
		int i = 0;
		for (final String f : featureOrder) {
			features[i++] = f;
		}
		try {
			composerExtension.buildFullFST(getArguments(configPath, basePath, outputPath, getContractParameter()), features);
		} catch (final TokenMgrError e) {
			createBuilderProblemMarker(getTokenMgrErrorLine(e.getMessage()), getTokenMgrErrorMessage(e.getMessage()));
		} catch (final Error e) {
			LOGGER.logError(e);
		}
		final ArrayList<FSTNode> fstnodes = composer.getFstnodes();
		if (fstnodes != null) {
			fhModelBuilder.buildModel(fstnodes, true);
		}
	}

	/**
	 * Returns the arguments for FeatureHouse Composer with the given arguments.
	 *
	 * @param configPath
	 * @param basePath
	 * @param outputPath
	 * @param contract
	 * @return
	 */
	private String[] getArguments(final String configPath, final String basePath, final String outputPath, String contract) {
		return new String[] { CmdLineInterpreter.INPUT_OPTION_EQUATIONFILE, configPath, CmdLineInterpreter.INPUT_OPTION_BASE_DIRECTORY, basePath,
			CmdLineInterpreter.INPUT_OPTION_OUTPUT_DIRECTORY, outputPath + "/", CmdLineInterpreter.INPUT_OPTION_CONTRACT_STYLE, contract,
			CmdLineInterpreter.INPUT_OPTION_NO_CONFIG_OUTPUT_DIR };
	}

	private String getContractParameter() {
		final String contractComposition = featureProject.getContractComposition().toLowerCase(Locale.ENGLISH);
		if (CONTRACT_COMPOSITION_NONE.equals(contractComposition)) {
			return CONTRACT_COMPOSITION_NONE;
		} else if (CONTRACT_COMPOSITION_PLAIN_CONTRACTING.equals(contractComposition)) {
			return CONTRACT_COMPOSITION_PLAIN_CONTRACT;
		} else if (CONTRACT_COMPOSITION_CONTRACT_OVERRIDING.equals(contractComposition)) {
			return CONTRACT_COMPOSITION_CONTRACT_OVERRIDING;
		} else if (CONTRACT_COMPOSITION_EXPLICIT_CONTRACT_REFINEMENT.equals(contractComposition)) {
			return CONTRACT_COMPOSITION_EXPLICIT_CONTRACTING;
		} else if (CONTRACT_COMPOSITION_CONSECUTIVE_CONTRACT_REFINEMENT.equals(contractComposition)) {
			return CONTRACT_COMPOSITION_CONSECUTIVE_CONTRACTING;
		} else if (CONTRACT_COMPOSITION_CUMULATIVE_CONTRACT_REFINEMENT.equals(contractComposition)) {
			return CONTRACT_COMPOSITION_CUMULATIVE_CONTRACTING;
		} else if (CONTRACT_COMPOSITION_CONJUNCTIVE_CONTRACT_REFINEMENT.equals(contractComposition)) {
			return CONTRACT_COMPOSITION_CONJUNCTIVE_CONTRACTING;
		} else if (CONTRACT_COMPOSITION_METHOD_BASED_COMPOSITION.equals(contractComposition)) {
			return CONTRACT_COMPOSITION_METHOD_BASED;
		}
		return CONTRACT_COMPOSITION_NONE;
	}

	public static final LinkedHashSet<String> EXTENSIONS = createExtensions();

	private static LinkedHashSet<String> createExtensions() {
		final LinkedHashSet<String> extensions = new LinkedHashSet<String>();
		extensions.add("asm");
		extensions.add("java");
		extensions.add("cs");
		extensions.add("c");
		extensions.add("h");
		extensions.add("hs");
		extensions.add("jj");
		extensions.add("als");
		extensions.add("xmi");
		return extensions;
	}

	@Override
	public LinkedHashSet<String> extensions() {
		return EXTENSIONS;
	}

	@Override
	public ArrayList<String[]> getTemplates() {
		return TEMPLATES;
	}

	private static final ArrayList<String[]> TEMPLATES = new ArrayList<String[]>(9);
	static {
		TEMPLATES.add(new String[] { "AsmetaL", "asm", "asm " + CLASS_NAME_PATTERN + " \n \n signature: \n \n definitions: \n" });
		TEMPLATES.add(new String[] { "Alloy", "als", "module " + CLASS_NAME_PATTERN });
		TEMPLATES.add(new String[] { "C", "c", "" });
		TEMPLATES.add(new String[] { "C#", "cs", "public class " + CLASS_NAME_PATTERN + " {\n\n}" });
		TEMPLATES.add(new String[] { "Haskell", "hs", "module " + CLASS_NAME_PATTERN + " where \n{\n\n}" });
		TEMPLATES.add(JAVA_TEMPLATE);
		TEMPLATES.add(new String[] { "JavaCC", "jj", "PARSER_BEGIN(" + CLASS_NAME_PATTERN + ") \n \n PARSER_END(" + CLASS_NAME_PATTERN + ")" });
		TEMPLATES.add(new String[] { "UML", "xmi",
			"<?xml version = '1.0' encoding = 'UTF-8' ?> \n	<XMI xmi.version = '1.2' xmlns:UML = 'org.omg.xmi.namespace.UML'>\n\n</XMI>" });
		TEMPLATES.add(new String[] { "Jak", "jak",
			"/**\r\n * TODO description\r\n */\r\npublic " + REFINES_PATTERN + " class " + CLASS_NAME_PATTERN + " {\r\n\r\n}" });
	}

	@Override
	public void postModelChanged() {
		checkContractComposition();
	}

	@Override
	public void postCompile(IResourceDelta delta, final IFile file) {
		super.postCompile(delta, file);

		try {
			if (!file.getWorkspace().isTreeLocked()) {
				file.refreshLocal(IResource.DEPTH_ZERO, null);
			}
			if (errorPropagation == null) {
				errorPropagation = ErrorPropagation.createErrorPropagation(file);
			}
			if (errorPropagation != null) {
				if (delta == null) {
					errorPropagation.force = true;
				}
				errorPropagation.addFile(file);
			}
		} catch (final CoreException e) {
			LOGGER.logError(e);
		}
	}

	@Override
	public int getDefaultTemplateIndex() {
		return 5;
	}

	@Override
	public void buildFSTModel() {
		if (featureProject == null) {
			return;
		}
		final String configPath;
		final IFile currentConfiguration = featureProject.getCurrentConfiguration();
		if (currentConfiguration != null) {
			final Path temporaryConfigrationFile = createTemporaryConfigrationFile(currentConfiguration);
			if (temporaryConfigrationFile == null) {
				return;
			}
			configPath = temporaryConfigrationFile.toString();
		} else {
			configPath = featureProject.getProject().getFile(".project").getRawLocation().toOSString();
		}
		final String basePath = featureProject.getSourcePath();
		final String outputPath = featureProject.getBuildPath();
		if ((configPath == null) || (basePath == null) || (outputPath == null)) {
			return;
		}

		final FSTGenComposerExtension composerExtension = new FSTGenComposerExtension();
		composer = composerExtension;
		composerExtension.addParseErrorListener(listener);

		final List<String> featureOrderList = featureProject.getFeatureModel().getFeatureOrderList();
		final String[] features = new String[featureOrderList.size()];
		int i = 0;
		for (final String f : featureOrderList) {
			features[i++] = f;
		}

		try {
			composerExtension.buildFullFST(getArguments(configPath, basePath, outputPath, getContractParameter()), features);
		} catch (final TokenMgrError e) {
			createBuilderProblemMarker(getTokenMgrErrorLine(e.getMessage()), getTokenMgrErrorMessage(e.getMessage()));
		} catch (final Error e) {
			LOGGER.logError(e);
		}

		final ArrayList<FSTNode> fstnodes = composer.getFstnodes();
		if (fstnodes != null) {
			fhModelBuilder.buildModel(fstnodes, false);
			fstnodes.clear();
		}
	}

	@Override
	public void buildConfiguration(IFolder folder, Configuration configuration, String congurationName) {
		super.buildConfiguration(folder, configuration, congurationName);
		final IFile configurationFile = folder.getFile(congurationName + '.' + getConfigurationExtension());
		final FSTGenComposer composer = new FSTGenComposer(false);
		composer.addParseErrorListener(createParseErrorListener());
		composer.addCompositionErrorListener(createCompositionErrorListener());
		final Path temporaryConfigrationFile = createTemporaryConfigrationFile(configurationFile);
		if (temporaryConfigrationFile == null) {
			return;
		}
		composer.run(
				getArguments(temporaryConfigrationFile.toString(), featureProject.getSourcePath(), folder.getLocation().toOSString(), getContractParameter()));
		if ((errorPropagation != null) && (errorPropagation.job != null)) {
			/*
			 * Waiting for the propagation job to finish, because the corresponding FSTModel is necessary for propagation at FH This is in general no problem
			 * because the compiler is much faster then the composer
			 */
			try {
				errorPropagation.job.join();
			} catch (final InterruptedException e) {
				LOGGER.logError(e);
			}
		}
		fhModelBuilder.buildModel(composer.getFstnodes(), false);
	}

	/**
	 * FeatureHouse causes access violation errors if it is executed parallel.
	 */
	@Override
	public boolean canGeneratInParallelJobs() {
		return false;
	}

	@Override
	public boolean hasContractComposition() {
		return true;
	}

	@Override
	public boolean hasMetaProductGeneration() {
		return true;
	}

	@Override
	public void copyNotComposedFiles(Configuration config, IFolder destination) {
		if (destination == null) {
			super.copyNotComposedFiles(config, featureProject.getBuildFolder());
		} else {
			// case: build into an external project
			super.copyNotComposedFiles(config, destination);
		}
	}

	@Override
	public Mechanism getGenerationMechanism() {
		return IComposerExtensionClass.Mechanism.FEATURE_ORIENTED_PROGRAMMING;
	}

	private void setProperty(QualifiedName qname, boolean value) {
		try {
			featureProject.getProject().setPersistentProperty(qname, value ? TRUE : FALSE);
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	private boolean getPropertyBoolean(QualifiedName qname) {
		try {
			return TRUE.equals(featureProject.getProject().getPersistentProperty(qname));
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return false;
	}

	public void setUseFuji(boolean useFuji) {
		// This is actually a quick fix until Fuji works on JRE8
		// Begin of Quick Fix
		final boolean jre8 = System.getProperty("java.runtime.version").substring(0, 3).equals("1.8");

		if (jre8) {
			MessageDialog.openInformation(null, "Information", "Fuji Typechecker is currently not supported for Java 1.8 runtime.");
			setProperty(USE_FUJI, false);
			return;
		}
		// End of Quick Fix

		setProperty(USE_FUJI, useFuji);

		if (useFuji) {
			final IFile currentConfiguration = featureProject.getCurrentConfiguration();
			if (currentConfiguration != null) {
				performFullBuild(currentConfiguration);
			}
		}
	}

	public boolean usesFuji() {
		return getPropertyBoolean(USE_FUJI);
	}

	public void setBuildMetaProduct(boolean value) {
		setProperty(BUILD_META_PRODUCT, value);
	}

	public final boolean buildMetaProduct() {
		return getPropertyBoolean(BUILD_META_PRODUCT);
	}

	@Override
	public boolean supportsMigration() {
		return true;
	}

	@Override
	public <T extends IComposerObject> T getComposerObjectInstance(Class<T> c) {
		if (c == ADocumentationCommentParser.class) {
			return c.cast(new DocumentationCommentParser());
		}
		return super.getComposerObjectInstance(c);
	}

	@Override
	public boolean needColor() {
		return true;
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
