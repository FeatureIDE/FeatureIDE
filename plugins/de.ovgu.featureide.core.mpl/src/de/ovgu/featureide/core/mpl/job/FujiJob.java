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
package de.ovgu.featureide.core.mpl.job;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.core.JavaProject;

import AST.ASTNode;
import AST.Access;
import AST.BodyDecl;
import AST.ClassDecl;
import AST.CompilationUnit;
import AST.ConstructorDecl;
import AST.FieldDeclaration;
import AST.ImportDecl;
import AST.InterfaceDecl;
import AST.List;
import AST.MemberClassDecl;
import AST.MemberInterfaceDecl;
import AST.MethodDecl;
import AST.ParameterDeclaration;
import AST.Program;
import AST.TypeDecl;
import beaver.Symbol;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.signature.ProjectSignatures;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractSignature.FeatureData;
import de.ovgu.featureide.core.mpl.signature.fuji.FujiClassSignature;
import de.ovgu.featureide.core.mpl.signature.fuji.FujiFieldSignature;
import de.ovgu.featureide.core.mpl.signature.fuji.FujiMethodSignature;
import de.ovgu.featureide.fm.core.FeatureModel;
import fuji.Composition;
import fuji.Main;

/**
 * Loads the signatures from Fuji.
 * 
 * @author Sebastian Krieter
 */
@SuppressWarnings("restriction")
public class FujiJob extends AMonitorJob {
	private final class SignatureReference {
		private final HashMap<Integer, FeatureData> ids = new HashMap<Integer, FeatureData>();
		private final AbstractSignature sig;

		public SignatureReference(AbstractSignature sig) {
			this.sig = sig;
		}
		
		public final FeatureData[] getFeatureData() {
			FeatureData[] ret = new FeatureData[ids.size()];
			int i = -1;
			for (FeatureData id : ids.values()) {
				ret[++i] = id;
			}
			return ret;
		}

		public final void addID(FeatureData featureData) {
			if (!ids.containsKey(featureData.getId())) {
				ids.put(featureData.getId(), featureData);
			}
		}

		public final AbstractSignature getSig() {
			return sig;
		}
	}

	private final ProjectSignatures projectSignatures = new ProjectSignatures();
	private final IFeatureProject featureProject;

	private final HashMap<AbstractSignature, SignatureReference> signatureSet = new HashMap<AbstractSignature, SignatureReference>();

	private Program ast = null;

	public FujiJob(IFeatureProject featureProject) {
		super("Loading Signatures");
		this.featureProject = featureProject;
		setPriority(BUILD);
	}

	private AbstractSignature addFeatureID(AbstractSignature sig, int featureID, int line) {
		SignatureReference sigRef = signatureSet.get(sig);
		if (sigRef == null) {
			sigRef = new SignatureReference(sig);
			signatureSet.put(sig, sigRef);
		}
		sigRef.addID(new FeatureData(featureID, line));
		return sigRef.getSig();
	}

	private static String getClassPaths(IFeatureProject featureProject) {
		String classpath = "";
		String sep = System.getProperty("path.separator");
		try {
			JavaProject proj = new JavaProject(featureProject.getProject(),
					null);
			IJavaElement[] elements = proj.getChildren();
			for (IJavaElement e : elements) {
				String path = e.getPath().toOSString();
				if (path.contains(":")) {
					classpath += sep + path;
					continue;
				}
				IResource resource = e.getResource();
				if (resource != null
						&& "jar".equals(resource.getFileExtension())) {
					classpath += sep + resource.getRawLocation().toOSString();
				}
			}
		} catch (JavaModelException e) {

		}
		return classpath.length() > 0 ? classpath.substring(1) : classpath;
	}

	private static java.util.List<String> featureModulePathnames = null;

	@SuppressWarnings("rawtypes")
	private static String getFeatureName(ASTNode astNode) {
		int featureID = astNode.featureID();

		String featurename = featureModulePathnames.get(featureID);
		return featurename.substring(featurename.lastIndexOf('\\') + 1);
	}

	@SuppressWarnings("unchecked")
	@Override
	protected boolean work() {
		FeatureModel fm = featureProject.getFeatureModel();
		fm.getAnalyser().setDependencies();

		String sourcePath = featureProject.getSourcePath();
		String[] fujiOptions = new String[] { 
				"-" + Main.OptionName.CLASSPATH, getClassPaths(featureProject)
				,"-" + Main.OptionName.PROG_MODE
				,"-" + Main.OptionName.COMPOSTION_STRATEGY, Main.OptionName.COMPOSTION_STRATEGY_ARG_FAMILY // "-typechecker",
				,"-" + Main.OptionName.BASEDIR, sourcePath};
		
		try {
			Main fuji = new Main(fujiOptions, fm, fm.getConcreteFeatureNames());
			Composition composition = fuji.getComposition(fuji);
			ast = composition.composeAST();
			fuji.typecheckAST(ast);
			featureModulePathnames = fuji.getSPLStructure().getFeatureModulePathnames();
		} catch (Exception e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}

		int count = 0;
		Iterator<CompilationUnit> unitIter = ast.compilationUnitIterator();
		while (unitIter.hasNext()) {
			if (unitIter.next().featureID() >= 0) {
				++count;
			}
		}
		setMaxAbsoluteWork(count);

		LinkedList<TypeDecl> stack = new LinkedList<TypeDecl>();
		LinkedList<AbstractClassSignature> roleStack = new LinkedList<AbstractClassSignature>();

		unitIter = ast.compilationUnitIterator();
		while (unitIter.hasNext()) {
			CompilationUnit unit = unitIter.next();
			if (unit.featureID() < 0) {
				continue;
			}
			String featurename = getFeatureName(unit);

			List<TypeDecl> typeDeclList = unit.getTypeDeclList();
			String pckg = unit.getPackageDecl();

			List<ImportDecl> importList = unit.getImportDeclList();

			for (TypeDecl rootTypeDecl : typeDeclList) {
				stack.push(rootTypeDecl);
				do {
					TypeDecl typeDecl = stack.pop();
					String name = typeDecl.name();
					String modifierString = typeDecl.getModifiers().toString();
					String typeString = null;

					if (typeDecl instanceof ClassDecl) {
						typeString = "class";
					} else if (typeDecl instanceof InterfaceDecl) {
						typeString = "interface";
					}

					AbstractClassSignature parent = null;
					if (!roleStack.isEmpty()) {
						parent = roleStack.pop();
					}
					featurename = getFeatureName(typeDecl);
					FujiClassSignature curClassSig = (FujiClassSignature) addFeatureID(
							new FujiClassSignature(parent, name,
									modifierString, typeString, pckg, typeDecl,
									importList),
							interfaceProject.getFeatureID(featurename), Symbol.getLine(typeDecl.getStart()));
					for (ImportDecl importDecl : importList) {
						curClassSig.addImport(importDecl.toString());
					}

					for (BodyDecl bodyDecl : typeDecl.getBodyDeclList()) {
						typeDecl.getModifiers();
						if (bodyDecl instanceof MethodDecl) {
							MethodDecl method = (MethodDecl) bodyDecl;

							modifierString = method.getModifiers().toString();
							name = method.name();
							TypeDecl type = method.type();

							List<ParameterDeclaration> parameterList = method
									.getParameterList();
							List<Access> exceptionList = method
									.getExceptionList();

							featurename = getFeatureName(bodyDecl);
							addFeatureID(new FujiMethodSignature(curClassSig,
									name, modifierString, type, false,
									parameterList, exceptionList), 
									interfaceProject.getFeatureID(featurename), Symbol.getLine(method.getStart()));

						} else if (bodyDecl instanceof FieldDeclaration) {
							FieldDeclaration field = (FieldDeclaration) bodyDecl;

							modifierString = field.getModifiers().toString();
							name = field.name();
							TypeDecl type = field.type();

							featurename = getFeatureName(bodyDecl);
							addFeatureID(new FujiFieldSignature(curClassSig,
									name, modifierString, type),
									interfaceProject.getFeatureID(featurename), Symbol.getLine(field.getStart()));

						} else if (bodyDecl instanceof ConstructorDecl) {
							ConstructorDecl constructor = (ConstructorDecl) bodyDecl;
							if (!constructor.isDefaultConstructor()) {
								modifierString = constructor.getModifiers()
										.toString();
								name = constructor.name();
								TypeDecl type = constructor.type();

								List<ParameterDeclaration> parameterList = constructor
										.getParameterList();
								List<Access> exceptionList = constructor
										.getExceptionList();

								featurename = getFeatureName(bodyDecl);
								addFeatureID(new FujiMethodSignature(
										curClassSig, name, modifierString,
										type, true, parameterList,
										exceptionList),
										interfaceProject.getFeatureID(featurename), Symbol.getLine(constructor.getStart()));
							}
							
						} else if (bodyDecl instanceof MemberClassDecl) {
							stack.push(((MemberClassDecl) bodyDecl)
									.getClassDecl());
							roleStack.push(curClassSig);
						} else if (bodyDecl instanceof MemberInterfaceDecl) {
							stack.push(((MemberInterfaceDecl) bodyDecl)
									.getInterfaceDecl());
							roleStack.push(curClassSig);
						}

					}
				} while (!stack.isEmpty());
			}
			worked();
		}

		final AbstractSignature[] sigArray = new AbstractSignature[signatureSet.size()];
		int i = -1;
		for (SignatureReference sigRef : signatureSet.values()) {
			AbstractSignature sig = sigRef.getSig();
			sig.setFeatureData(sigRef.getFeatureData());
			sigArray[++i] = sig;
		}
		projectSignatures.setSignatureArray(sigArray);
		interfaceProject.setProjectSignatures(projectSignatures);
		
		MPLPlugin.getDefault().logInfo("Fuji signatures loaded.");
		return true;
	}
}
