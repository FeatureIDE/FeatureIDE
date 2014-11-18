/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import javax.swing.JOptionPane;

import org.apache.commons.cli.ParseException;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;

import AST.Program;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.mpl.InterfaceProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.job.ExtendedFujiSignaturesJob;
import de.ovgu.featureide.core.mpl.job.JobManager;
import de.ovgu.featureide.core.mpl.signature.ProjectSignatures;
import de.ovgu.featureide.core.mpl.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractFieldSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractMethodSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractSignature;
import de.ovgu.featureide.core.mpl.signature.filter.MethodFilter;
import de.ovgu.featureide.featurehouse.FeatureHouseComposer;
import de.ovgu.featureide.featurehouse.FeatureHouseCorePlugin;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.uka.ilkd.key.gui.GUIEvent;
import de.uka.ilkd.key.gui.GUIListener;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.Main;
import fuji.CompilerWarningException;
import fuji.Composition;
import fuji.FeatureDirNotFoundException;
import fuji.SemanticErrorException;
import fuji.SyntacticErrorException;

/**
 * Generates Feature Stubs
 * 
 * @author Stefan Krueger
 */
public class FeatureStubsGenerator {

	private String PATH; // = "D" + Path.DEVICE_SEPARATOR + "\\FeatureIDETEST\\";
	private IFeatureProject featureProject = null;

	private GUIListener guiL = null;
	private IFolder featureStubFolder = null;
	
	public FeatureStubsGenerator(IFeatureProject fProject) {
		this.featureProject = fProject;
		PATH = featureProject.getProject().getLocation().toOSString() + File.separator + featureProject.getFeaturestubPath() + File.separator;
	}
	
	public boolean generate() {
		if (featureProject.getFSTModel() == null) {
			featureProject.getComposer().initialize(featureProject);
			featureProject.getComposer().buildFSTModel();
		}
		final ExtendedFujiSignaturesJob fujiSignaturesJob = new ExtendedFujiSignaturesJob();

		String fhc = FeatureHouseComposer.getClassPaths(featureProject);
		String[] fujiOptions = new String[] { "-" + fuji.Main.OptionName.CLASSPATH, fhc, "-" + fuji.Main.OptionName.PROG_MODE, "-" + fuji.Main.OptionName.COMPOSTION_STRATEGY,
				fuji.Main.OptionName.COMPOSTION_STRATEGY_ARG_FAMILY, "-typechecker", "-basedir", featureProject.getSourcePath() };
		FeatureModel fm = featureProject.getFeatureModel();
		fm.getAnalyser().setDependencies();

		try {
			fuji.Main fuji = new fuji.Main(fujiOptions, fm, featureProject.getFeatureModel().getConcreteFeatureNames());
			Composition composition = fuji.getComposition(fuji);
			Program ast = composition.composeAST();
			// run type check
			fuji.typecheckAST(ast);
			
			if (!fuji.getWarnings().isEmpty()) {
				FeatureHouseCorePlugin.getDefault().logError("The SPL " + featureProject.getProjectName() + " contains type errors. Therefore, the verification is aborted.", null);
			}
		} catch (IllegalArgumentException | ParseException | IOException | FeatureDirNotFoundException | SyntacticErrorException
				| SemanticErrorException | CompilerWarningException | UnsupportedModelException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		
		
		final Object tmpObject = new Object();
		final InterfaceProject intProject = MPLPlugin.getDefault().addProject(featureProject.getProject());
		fujiSignaturesJob.setProject(intProject.getProjectReference());
		Thread buildThread;
		buildThread = new Thread(new Runnable() {
			@Override
			public void run() {
				JobManager.addJob(tmpObject, fujiSignaturesJob);
				// wait for jobs to be finished
				synchronized (tmpObject) {
					try {
						tmpObject.wait();
					} catch (InterruptedException e) {
						CorePlugin.getDefault().logError(e);
					} finally {
					}
				}
			}
		});
		buildThread.start();
		try {
			buildThread.join();
		} catch (InterruptedException e) {
			CorePlugin.getDefault().logError(e);
		}

		final ProjectSignatures signatures = fujiSignaturesJob.getProjectSignatures();
//		file = null;

		Thread stubThread = new Thread() {

			@Override
			public void run() {
				getFeatures(signatures, intProject);
			}

		};
		stubThread.setPriority(Thread.MAX_PRIORITY);
		stubThread.start();
		
		return true;
	}

	private void createFeatureStub(final FSTFeature feat, final ProjectSignatures signatures, final InterfaceProject intProject) {
		Thread keyThread = new Thread() {
			public void run() {
				try {
					File file = null;
					String fileText = "";
					int featureID = intProject.getFeatureID(feat.getName());
					CorePlugin.createFolder(featureProject.getProject(), featureProject.getFeaturestubPath() + File.separator + feat.getName());
					final HashSet<String> alreadyUsedSigs = new HashSet<String>();
					copyRolesToFeatureStubsFolder(feat);
					
					for (FSTRole role : feat.getRoles()) {
						file = new File(PATH + File.separator + feat.getName() + File.separator + role.getClassFragment().getName());
						fileText = new String(Files.readAllBytes(Paths.get(file.getPath())));

						final int lastIndexOf = fileText.lastIndexOf("}");
						if (lastIndexOf < 0) {
							FeatureHouseCorePlugin.getDefault().logError("Class " + file.getAbsolutePath() + " is not complete.", null);
							return;
						}
						StringBuilder fileTextSB = new StringBuilder(fileText.substring(0, lastIndexOf));
						for (FSTMethod meth : role.getClassFragment().getMethods()) {
							final SignatureIterator sigIterator = signatures.createIterator();
							sigIterator.addFilter(new MethodFilter());

							while (sigIterator.hasNext()) {
								AbstractSignature curSig = sigIterator.next();
								for (int i = 0; i < curSig.getFeatureData().length; i++) {
									if (curSig.getFeatureData()[i].getId() == featureID && curSig.getName().equals(meth.getName())
											&& curSig.getFeatureData()[i].getLineNumber() == meth.getLine()) {
										if (curSig.getFeatureData()[i].usesExternMethods()) {
											FeatureHouseCorePlugin.getDefault().logError("The method\n"	+ curSig.getFullName() + "\nis not defined within the currently checked SPL. Therefore the process will be aborted."
															, null);
											return;
										}
										
										if (curSig.getFeatureData()[i].usesOriginal()) {
											fileTextSB = checkForOriginal(fileTextSB, meth, curSig, intProject.getFeatureName(curSig.getFeatureData()[i].getId()));
										}

										if (meth.hasContract() && meth.getContract().contains("\\original")) {
											fileTextSB = checkForOriginalInContract(fileTextSB, curSig);
										}
										
										for (String typeName : curSig.getFeatureData()[i].getUsedNonPrimitveTypes()) {
											checkForMissingTypes(feat, role, typeName);
										}
										
										Set<AbstractSignature> calledSignatures = new HashSet<AbstractSignature>(curSig.getFeatureData()[i].getCalledSignatures());
										for (AbstractSignature innerAbs : calledSignatures) {
											if (!isInCurrentFeature(featureID, innerAbs) && alreadyUsedSigs.add(innerAbs.toString())) {
												if (innerAbs.getParent().getName().equals(role.getClassFragment().getName().substring(0, role.getClassFragment().getName().indexOf(".")))) {
													createPrototypes(fileTextSB, innerAbs);
												} else {
													File newClassFile = new File(PATH + feat.getName() + "\\" + innerAbs.getParent().getName() + ".java");
													StringBuilder newClassFileTextSB = createClassForPrototype(innerAbs, newClassFile);
													createPrototypes(newClassFileTextSB, innerAbs);
													newClassFileTextSB.append("\n}");
													writeToFile(newClassFile, newClassFileTextSB);
												}
											}
										}
									}
								}
							}
						}
						fileTextSB.append(fileText.substring(lastIndexOf));
						writeToFile(file, fileTextSB);
					}
					Main key = new Main(new String[] { file.getCanonicalPath() });
					if (key.getUi() != null) {
						KeYMediator m = key.getUi().getMediator();
						m.addGUIListener(guiL);
					} else {
						FeatureHouseCorePlugin.getDefault().logError("KeY could not be started.", null);
					}
				} catch (IOException e) {
					FeatureHouseCorePlugin.getDefault().logError(e);
				}
			}
		};
		keyThread.start();

	}
	
	private void getFeatures(final ProjectSignatures signatures, final InterfaceProject intProject) {
		final LinkedList<FSTFeature> features = new LinkedList<FSTFeature>(this.featureProject.getFSTModel().getFeatures());
		featureStubFolder = CorePlugin.createFolder(featureProject.getProject(), featureProject.getFeaturestubPath());
		for (FSTFeature fstfeat : features) {
			try {
				featureStubFolder.getFolder(fstfeat.getName()).delete(true, null);
			} catch (CoreException e1) {
				FeatureHouseCorePlugin.getDefault().logError(e1);
			}
		}
		
		
		guiL = new GUIListener() {

			@Override
			public void modalDialogOpened(GUIEvent e) {
			}

			@Override
			public void modalDialogClosed(GUIEvent e) {
			}

			@Override
			public void shutDown(GUIEvent e) {
				nextElement(signatures, intProject, features);
			}
		};
		nextElement(signatures, intProject, features);
	}

	private void nextElement(final ProjectSignatures signatures, final InterfaceProject intProject, final LinkedList<FSTFeature> features) {
		if (!features.isEmpty()) {
			FSTFeature fstFeat;
			while (!(fstFeat = features.removeFirst()).hasMethodContracts()) {};
			createFeatureStub(fstFeat, signatures, intProject); 
		} else {
			FeatureHouseCorePlugin.getDefault().logInfo("Feature Stubs generated and proven.");
		}
	}
	
	private StringBuilder createClassForPrototype(AbstractSignature absStig, File classFile) {
		StringBuilder newClassFileTextSB = null;
		try {
			classFile.createNewFile();
			String newClassFileText = new String(Files.readAllBytes(classFile.toPath()));
			final int lastIndexInNewClassFile = newClassFileText.lastIndexOf("}");
			newClassFileTextSB = new StringBuilder(newClassFileText.substring(0,
					lastIndexInNewClassFile > -1 ? lastIndexInNewClassFile : newClassFileText.length()));

			if ((newClassFileTextSB.length() == 0)) {
				newClassFileTextSB.append("public class " + absStig.getParent().getName() + "{\n");
			}
		} catch (IOException e1) {
			FeatureHouseCorePlugin.getDefault().logError(e1);
		}
		return newClassFileTextSB;
	}

	private void createPrototypes(StringBuilder fileTextSB, AbstractSignature innerAbs) {
		if (innerAbs instanceof AbstractMethodSignature) {
			fileTextSB.append("\n\n\t/*method prototype*/" + "\t/*@\n\t@ requires_abs   " + innerAbs.getName()
					+ "R;\n\t@ ensures_abs    " + innerAbs.getName()
					+ "E;\n\t@ assignable_abs " + innerAbs.getName() + "A;\n\t@*/\n"
					+ innerAbs.toString() + "{" + "}\n");
		} else if (innerAbs instanceof AbstractFieldSignature) {
			fileTextSB.append("/*field prototype*/\n"
					+ innerAbs.toString() + ";\n");
		}
	}

	private boolean isInCurrentFeature(int featureID, AbstractSignature innerAbs) {
		for (int j = 0; j < innerAbs.getFeatureData().length; j++) {
			if (innerAbs.getFeatureData()[j].getId() == featureID) {
				return true;
			}
		}
		return false;
	}

	private void checkForMissingTypes(final FSTFeature feature, FSTRole role, String className) {
		if (featureStubFolder.getFolder(role.getFeature().getName()).getFile(className + ".java").exists())
			return;
		File missingTypeFile = new File(PATH + feature.getName() + "\\" + className + ".java");
		StringBuilder missingTypeFileTextSB = null;
		try {
			missingTypeFile.createNewFile();
			String missingTypeFileText = new String(Files.readAllBytes(missingTypeFile.toPath()));
			final int lastIndexInNewClassFile = missingTypeFileText.lastIndexOf("}");
			missingTypeFileTextSB = new StringBuilder(missingTypeFileText.substring(0,
					lastIndexInNewClassFile > -1 ? lastIndexInNewClassFile : missingTypeFileText.length()));

			if ((missingTypeFileTextSB.length() == 0)) {
				missingTypeFileTextSB.append("public class " + className + "{}");
				writeToFile(missingTypeFile, missingTypeFileTextSB);
			}
		} catch (IOException e1) {
			FeatureHouseCorePlugin.getDefault().logError(e1);
		}
	}

	private void writeToFile(File File, StringBuilder Text) {
		FileWriter newClassWriter = null;
		try {
			newClassWriter = new FileWriter(File);
			newClassWriter.write(Text.toString());
		} catch (IOException e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		} finally {
			try {
				if (newClassWriter != null) {
					newClassWriter.close();
				}
			} catch (IOException e) {
				FeatureHouseCorePlugin.getDefault().logError(e);
			}
		}
	}

	private StringBuilder checkForOriginalInContract(StringBuilder fileTextSB, AbstractSignature curSig) {
		final int indexOfBody = fileTextSB.indexOf(curSig.toString().trim());
		String tmpText = fileTextSB.substring(0, indexOfBody);
		final int indexOfStartOfContract = tmpText.lastIndexOf("/*@");
		final String contractBody = fileTextSB.substring(tmpText.length() - 1);
		String tmpFileText = fileTextSB.substring(0, indexOfStartOfContract)
				+ "\n\n\t/*@\n\t@ requires_abs   " + curSig.getName() + "R;\n\t@ ensures_abs    "
				+ curSig.getName() + "E;\n\t@ assignable_abs " + curSig.getName() + "A;\n\t@*/\n"
				+ contractBody;
		return new StringBuilder(tmpFileText);
	}

	private StringBuilder checkForOriginal(StringBuilder fileTextSB, FSTMethod meth, AbstractSignature curSig,
			final String featureName) {
		final String absMethodName = curSig.toString();
		final int indexOf = absMethodName.indexOf("(");
		final String methodName = absMethodName.substring(0, indexOf) + "_original_" + featureName
				+ absMethodName.substring(indexOf);
		fileTextSB.append("\n\n\t/*@\n\t@ requires_abs   " + curSig.getName() + "_original_"
				+ featureName + "R;\n\t@ ensures_abs    " + curSig.getName() + "_original_"
				+ featureName + "E;\n\t@ assignable_abs " + curSig.getName() + "_original_"
				+ featureName + "A;\n\t@*/\n" + methodName + "{" + "}\n");
		
		final int indexOfBody = fileTextSB.indexOf(meth.getBody());
		final int indexOfOriginal = fileTextSB.substring(indexOfBody).indexOf("original(");
		final String methodBody = fileTextSB.substring(indexOfBody + indexOfOriginal);
		String tmpFileText = fileTextSB.substring(0, indexOfBody + indexOfOriginal) + curSig.getName()
				+ "_original_" + featureName + methodBody.substring(methodBody.indexOf("(")); 
		return new StringBuilder(tmpFileText);
	}

	private void copyRolesToFeatureStubsFolder(final FSTFeature feat) {
		for (FSTRole role: feat.getRoles()) {
			final String pathString = featureProject.getFeaturestubPath() + File.separator + feat.getName() + File.separator
					+ role.getClassFragment().getName();
			
			IPath path = new Path(pathString);
			IFile newRole = featureProject.getProject().getFile(path);
			try {
				role.getFile().copy(newRole.getFullPath(), true, null);
			} catch (CoreException e) {
				FeatureHouseCorePlugin.getDefault().logError(e);
			}
		}
	}

	@Override
	public String toString() {
		return "Feature Stub Generator for " + this.featureProject.getProjectName() + "."; 
	}
}
