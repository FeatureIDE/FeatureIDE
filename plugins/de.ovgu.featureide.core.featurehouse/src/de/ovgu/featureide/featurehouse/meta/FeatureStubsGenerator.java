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
package de.ovgu.featureide.featurehouse.meta;

import static de.ovgu.featureide.fm.core.localization.StringTable.ASSIGNABLE;
import static de.ovgu.featureide.fm.core.localization.StringTable.CLASS;
import static de.ovgu.featureide.fm.core.localization.StringTable.ENSURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURE_STUBS_GENERATED_AND_PROVEN_;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURE_STUB_GENERATOR_FOR;
import static de.ovgu.featureide.fm.core.localization.StringTable.IS_NOT_COMPLETE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.PLEASE_INSTALL_KEY_FOR_AN_AUTO_START_OF_THE_THEOREM_PROVER_;
import static de.ovgu.featureide.fm.core.localization.StringTable.REQUIRES;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.base.AbstractFieldSignature;
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.FOPFeatureData;
import de.ovgu.featureide.core.signature.filter.MethodFilter;
import de.ovgu.featureide.featurehouse.ExtendedFujiSignaturesJob;
import de.ovgu.featureide.featurehouse.FeatureHouseCorePlugin;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.job.IJob;
import de.ovgu.featureide.fm.core.job.IRunner;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.util.JobFinishListener;

/**
 * Generates Feature Stubs
 *
 * @author Stefan Krueger
 * @author Marcus Pinnecke (Feature Interface)
 */
public class FeatureStubsGenerator {

	private final String PATH;
	private IFeatureProject featureProject = null;

	KeYWrapper keyWrapper = null;
	private IFolder featureStubFolder = null;

	public FeatureStubsGenerator(IFeatureProject fProject) {
		featureProject = fProject;
		PATH = featureProject.getProject().getLocation().toOSString() + File.separator + featureProject.getFeaturestubPath() + File.separator;
	}

	public boolean generate() {
		if (featureProject.getFSTModel() == null) {
			featureProject.getComposer().buildFSTModel();
		}

//		String fhc = FeatureHouseComposer.getClassPaths(featureProject);
//		String[] fujiOptions = new String[] { "-" + fuji.Main.OptionName.CLASSPATH, fhc, "-" + fuji.Main.OptionName.PROG_MODE, "-" + fuji.Main.OptionName.COMPOSTION_STRATEGY,
//				fuji.Main.OptionName.COMPOSTION_STRATEGY_ARG_FAMILY, "-typechecker", "-basedir", featureProject.getSourcePath() };
		final IFeatureModel fm = featureProject.getFeatureModel();
		fm.getAnalyser().setDependencies();

//		try {
//			fuji.Main fuji = new fuji.Main(fujiOptions, fm, featureProject.getFeatureModel().getConcreteFeatureNames());
//			Composition composition = fuji.getComposition(fuji);
//			Program ast = composition.composeAST();
//			// run type check
//			fuji.typecheckAST(ast);
//
//			if (!fuji.getWarnings().isEmpty()) {
//				FeatureHouseCorePlugin.getDefault().logError("The SPL " + featureProject.getProjectName() + " contains type errors. Therefore, the verification is aborted.", null);
//			}
//		} catch (IllegalArgumentException | ParseException | IOException | FeatureDirNotFoundException | SyntacticErrorException
//				| SemanticErrorException | CompilerWarningException | UnsupportedModelException e1) {
//			FeatureHouseCorePlugin.getDefault().logError(e1);
//		}

		final IRunner<ProjectSignatures> efsj = LongRunningWrapper.getRunner(new ExtendedFujiSignaturesJob(featureProject));
		efsj.addJobFinishedListener(new JobFinishListener<ProjectSignatures>() {

			@Override
			public void jobFinished(IJob<ProjectSignatures> finishedJob) {
				getFeatures(featureProject.getFSTModel().getProjectSignatures());
			}

		});
		efsj.schedule();

		return true;
	}

	private void createFeatureStub(final FSTFeature feat, final ProjectSignatures signatures) {
		final Thread keyThread = new Thread() {

			@Override
			public void run() {
				try {
					File file = null;
					String fileText = "";
					final int featureID = signatures.getFeatureID(feat.getName());
					CorePlugin.createFolder(featureProject.getProject(), featureProject.getFeaturestubPath() + File.separator + feat.getName());
					final HashSet<String> alreadyUsedSigs = new HashSet<String>();
					copyRolesToFeatureStubsFolder(feat);

					for (final FSTRole role : feat.getRoles()) {
						file = new File(PATH + File.separator + feat.getName() + File.separator + role.getClassFragment().getName());
						fileText = new String(Files.readAllBytes(Paths.get(file.getPath())));

						final int lastIndexOf = fileText.lastIndexOf("}");
						if (lastIndexOf < 0) {
							FeatureHouseCorePlugin.getDefault().logError(CLASS + file.getAbsolutePath() + IS_NOT_COMPLETE_, null);
							return;
						}
						StringBuilder fileTextSB = new StringBuilder(fileText.substring(0, lastIndexOf));

						for (final FSTMethod meth : role.getClassFragment().getMethods()) {
							boolean contractChanged = false;
							final SignatureIterator sigIterator = signatures.iterator();
							sigIterator.addFilter(new MethodFilter());

							while (sigIterator.hasNext()) {
								final AbstractSignature curSig = sigIterator.next();
								for (int i = 0; i < curSig.getFeatureData().length; i++) {
									if (((curSig.getFeatureData())[i].getID() == featureID) && curSig.getName().equals(meth.getName())
										&& (curSig.getFeatureData()[i].getStartLineNumber() == meth.getLine())) {
										if (((FOPFeatureData[]) curSig.getFeatureData())[i].usesExternMethods()) {
											FeatureHouseCorePlugin.getDefault().logError("The method\n" + curSig.getFullName()
												+ "\nis not defined within the currently checked SPL. Therefore the process will be aborted.", null);
											return;
										}

										if (((FOPFeatureData[]) curSig.getFeatureData())[i].usesOriginal()) {
											fileTextSB = checkForOriginal(fileTextSB, meth, curSig,
													signatures.getFeatureName(((FOPFeatureData[]) curSig.getFeatureData())[i].getID()));
										}

										if (meth.hasContract() && meth.getContract().contains("\\original")) {
											contractChanged = true;
											// fileTextSB = checkForOriginalInContract(fileTextSB, curSig);
										}

										for (final String typeName : ((FOPFeatureData[]) curSig.getFeatureData())[i].getUsedNonPrimitveTypes()) {
											checkForMissingTypes(feat, role, typeName);
										}

										final Set<AbstractSignature> calledSignatures =
											new HashSet<AbstractSignature>(((FOPFeatureData[]) curSig.getFeatureData())[i].getCalledSignatures());
										for (final AbstractSignature innerAbs : calledSignatures) {
											if (!isInCurrentFeature(featureID, innerAbs) && alreadyUsedSigs.add(innerAbs.toString())) {
												if (innerAbs.getParent().getName().equals(
														role.getClassFragment().getName().substring(0, role.getClassFragment().getName().indexOf(".")))) {
													createPrototypes(fileTextSB, innerAbs);
												} else {
													final File newClassFile = new File(PATH + feat.getName() + "\\" + innerAbs.getParent().getName() + ".java");
													final StringBuilder newClassFileTextSB = createClassForPrototype(innerAbs, newClassFile);
													createPrototypes(newClassFileTextSB, innerAbs);
													newClassFileTextSB.append("\n}");
													writeToFile(newClassFile, newClassFileTextSB.toString());
												}
											}
										}
										if (!contractChanged && meth.hasContract()) {
											fileTextSB = transformIntoAbstractContract(fileTextSB, curSig);
										}
									}
								}
							}
						}

						fileTextSB.append(fileText.substring(lastIndexOf));
						writeToFile(file, fileTextSB.toString());
					}
					if (keyWrapper != null) {
						keyWrapper.runKeY(file);
					}
				} catch (final IOException e) {
					FeatureHouseCorePlugin.getDefault().logError(e);
				}
			}
		};
		keyThread.start();

	}

	private void getFeatures(final ProjectSignatures signatures) {
		final LinkedList<FSTFeature> features = new LinkedList<FSTFeature>(featureProject.getFSTModel().getFeatures());
		featureStubFolder = CorePlugin.createFolder(featureProject.getProject(), featureProject.getFeaturestubPath());
		for (final FSTFeature fstfeat : features) {
			try {
				featureStubFolder.getFolder(fstfeat.getName()).delete(true, null);
			} catch (final CoreException e1) {
				FeatureHouseCorePlugin.getDefault().logError(e1);
			}
		}
		keyWrapper = KeYWrapper.createGUIListener(this, signatures, features);

		if (keyWrapper == null) {
			FeatureHouseCorePlugin.getDefault().logInfo(PLEASE_INSTALL_KEY_FOR_AN_AUTO_START_OF_THE_THEOREM_PROVER_);
			while (!features.isEmpty()) {
				nextElement(signatures, features);
			}
		} else {
			nextElement(signatures, features);
		}
	}

	void nextElement(final ProjectSignatures signatures, final LinkedList<FSTFeature> features) {
		if (!features.isEmpty()) {
			FSTFeature fstFeat;
			while (!(fstFeat = features.removeFirst()).hasMethodContracts()) {}
			;
			createFeatureStub(fstFeat, signatures);
		} else {
			FeatureHouseCorePlugin.getDefault().logInfo(FEATURE_STUBS_GENERATED_AND_PROVEN_);
		}
	}

	private StringBuilder createClassForPrototype(AbstractSignature absStig, File classFile) {
		StringBuilder newClassFileTextSB = null;
		try {
			if (classFile.createNewFile()) {
				newClassFileTextSB = new StringBuilder("public class " + absStig.getParent().getName() + "{\n");
			} else {
				final String newClassFileText = new String(Files.readAllBytes(classFile.toPath()));
				final int lastIndexInNewClassFile = newClassFileText.lastIndexOf("}");
				newClassFileTextSB =
					new StringBuilder(newClassFileText.substring(0, lastIndexInNewClassFile > -1 ? lastIndexInNewClassFile : newClassFileText.length()));
			}
		} catch (final IOException e1) {
			FeatureHouseCorePlugin.getDefault().logError(e1);
		}
		return newClassFileTextSB;
	}

	private void createPrototypes(StringBuilder fileTextSB, AbstractSignature innerAbs) {
		if (innerAbs instanceof AbstractMethodSignature) {
			fileTextSB.append("\n\n\t/*method prototype*/" + "\t/*@\n\t@ requires_abs   " + innerAbs.getName() + "R;\n\t@ ensures_abs    " + innerAbs.getName()
				+ "E;\n\t@ assignable_abs " + innerAbs.getName() + "A;\n\t@*/\n" + innerAbs.toString() + "{" + "}\n");
		} else if (innerAbs instanceof AbstractFieldSignature) {
			fileTextSB.append("/*field prototype*/\n" + innerAbs.toString() + ";\n");
		}
	}

	private boolean isInCurrentFeature(int featureID, AbstractSignature innerAbs) {
		for (int j = 0; j < innerAbs.getFeatureData().length; j++) {
			if ((innerAbs.getFeatureData())[j].getID() == featureID) {
				return true;
			}
		}
		return false;
	}

	private void checkForMissingTypes(final FSTFeature feature, FSTRole role, String className) {
		if (featureStubFolder.getFolder(role.getFeature().getName()).getFile(className + ".java").exists()) {
			return;
		}
		final File missingTypeFile = new File(PATH + feature.getName() + "\\" + className + ".java");
		try {
			if (missingTypeFile.createNewFile()) {
				writeToFile(missingTypeFile, "public class " + className + "{}");
			} else {
				final String missingTypeFileText = new String(Files.readAllBytes(missingTypeFile.toPath()));
				final int lastIndexInNewClassFile = missingTypeFileText.lastIndexOf("}");
				final StringBuilder missingTypeFileTextSB =
					new StringBuilder(missingTypeFileText.substring(0, lastIndexInNewClassFile > -1 ? lastIndexInNewClassFile : missingTypeFileText.length()));
				writeToFile(missingTypeFile, missingTypeFileTextSB.toString());
			}
		} catch (final IOException e1) {
			FeatureHouseCorePlugin.getDefault().logError(e1);
		}
	}

	private void writeToFile(File file, String text) {
		FileWriter newClassWriter = null;
		try {
			newClassWriter = new FileWriter(file);
			newClassWriter.write(text);
		} catch (final IOException e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		} finally {
			try {
				if (newClassWriter != null) {
					newClassWriter.close();
				}
			} catch (final IOException e) {
				FeatureHouseCorePlugin.getDefault().logError(e);
			}
		}
	}

//	private StringBuilder checkForOriginalInContract(StringBuilder fileTextSB, AbstractSignature curSig) {
//		final int indexOfBody = fileTextSB.indexOf(curSig.toString().trim());
//		String tmpText = fileTextSB.substring(0, indexOfBody);
//		final int indexOfStartOfContract = tmpText.lastIndexOf("/*@");
//		final String contractBody = fileTextSB.substring(tmpText.length() - 1);
//		String tmpFileText = fileTextSB.substring(0, indexOfStartOfContract)
//				+ "\n\n\t/*@\n\t@ requires_abs   " + curSig.getName() + "R;\n\t@ ensures_abs    "
//				+ curSig.getName() + "E;\n\t@ assignable_abs " + curSig.getName() + "A;\n\t@*/\n"
//				+ contractBody;
//		return new StringBuilder(tmpFileText);
//	}

	private StringBuilder transformIntoAbstractContract(StringBuilder fileTextSB, AbstractSignature curSig) {
		int indexOfBody = fileTextSB.toString().lastIndexOf(curSig.toString().trim());
		if (indexOfBody < 1) {
			indexOfBody = fileTextSB.toString().lastIndexOf(" " + curSig.getName() + "(");
		}
		final String tmpText = fileTextSB.substring(0, indexOfBody);
		int indexOfStartOfContract = tmpText.lastIndexOf("/*@");
		String contractBody = "";
		while (!(contractBody.contains(ENSURES) || contractBody.contains(REQUIRES) || contractBody.contains(ASSIGNABLE))) {
			if (!contractBody.isEmpty()) {
				indexOfStartOfContract = fileTextSB.substring(0, fileTextSB.indexOf(contractBody) - 2).lastIndexOf("/*@");
			}
			if (indexOfStartOfContract < 0) {
				return null;
			}
			contractBody = fileTextSB.substring(indexOfStartOfContract);
		}
		contractBody = contractBody.substring(0, contractBody.indexOf("*/"));
		final StringBuilder ensures = new StringBuilder(), requires = new StringBuilder(), assignable = new StringBuilder();
		final String[] contracts = contractBody.split("\n");
		for (int i = 0; i < contracts.length; i++) {
			final String line = contracts[i].replace("@", "").trim();
			if (line.startsWith(REQUIRES)) {
				i = aggregateClauses(requires, contracts, i, line);
			} else if (line.startsWith(ENSURES)) {
				i = aggregateClauses(ensures, contracts, i, line);
			} else if (line.startsWith(ASSIGNABLE)) {
				assignable.append(line.replace(ASSIGNABLE, ""));
			}
		}
		final String tmpFileText = fileTextSB.substring(0, indexOfStartOfContract) + "/*@\n" + "\t@ requires_abs   " + curSig.getName() + "R;\n"
			+ ((requires.length() != 0) ? "\t@ def " + curSig.getName() + "R = " + requires.toString().replace(";", "") + ";\n" : "") + "\t@ ensures_abs "
			+ curSig.getName() + "E;\n" + ((ensures.length() != 0) ? "\t@ def " + curSig.getName() + "E = " + ensures.toString().replace(";", "") + ";\n" : "")
			+ "\t@ assignable_abs " + curSig.getName() + "A;\n"
			+ ((assignable.length() != 0) ? "\t@ def " + curSig.getName() + "A = " + assignable.toString() + "\n" : "") + "\t@"
			+ fileTextSB.substring(indexOfStartOfContract + contractBody.length());
		return new StringBuilder(tmpFileText);
	}

	private int aggregateClauses(StringBuilder clause, String[] contracts, int i, String line) {
		if (clause.length() > 0) {
			clause.append(" && ");
		}
		clause.append("(");
		clause.append(line.substring(line.indexOf(" ")));
		while (!line.endsWith(";")) {
			line = contracts[++i].replace("@", "").trim();
			clause.append(line);
		}

		clause.append(")");
		return i;
	}

	private StringBuilder checkForOriginal(StringBuilder fileTextSB, FSTMethod meth, AbstractSignature curSig, final String featureName) {
		final String absMethodName = curSig.toString();
		final int indexOf = absMethodName.indexOf("(");
		final String methodName = absMethodName.substring(0, indexOf) + "_original_" + featureName + absMethodName.substring(indexOf);
		fileTextSB.append(
				"\n\n\t/*@\n\t@ requires_abs   " + curSig.getName() + "_original_" + featureName + "R;\n\t@ ensures_abs    " + curSig.getName() + "_original_"
					+ featureName + "E;\n\t@ assignable_abs " + curSig.getName() + "_original_" + featureName + "A;\n\t@*/\n" + methodName + "{" + "}\n");

		final int indexOfBody = fileTextSB.indexOf(meth.getBody());
		final int indexOfOriginal = fileTextSB.substring(indexOfBody).indexOf("original(");
		final String methodBody = fileTextSB.substring(indexOfBody + indexOfOriginal);
		final String tmpFileText = fileTextSB.substring(0, indexOfBody + indexOfOriginal) + curSig.getName() + "_original_" + featureName
			+ methodBody.substring(methodBody.indexOf("("));
		return new StringBuilder(tmpFileText);
	}

	private void copyRolesToFeatureStubsFolder(final FSTFeature feat) {
		for (final FSTRole role : feat.getRoles()) {
			final String pathString =
				featureProject.getFeaturestubPath() + File.separator + feat.getName() + File.separator + role.getClassFragment().getName();

			final IPath path = new Path(pathString);
			final IFile newRole = featureProject.getProject().getFile(path);
			try {
				role.getFile().copy(newRole.getFullPath(), true, null);
			} catch (final CoreException e) {
				FeatureHouseCorePlugin.getDefault().logError(e);
			}
		}
	}

	@Override
	public String toString() {
		return FEATURE_STUB_GENERATOR_FOR + featureProject.getProjectName() + ".";
	}
}
