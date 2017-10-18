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

import java.io.File;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;

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
import AST.Modifier;
import AST.ParameterDeclaration;
import AST.Program;
import AST.TypeDecl;
import beaver.Symbol;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.fstmodel.IRoleElement;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.FOPFeatureData;
import de.ovgu.featureide.core.signature.base.FeatureDataConstructor;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiClassSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiFieldSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;

/**
 * Loads the signatures from Fuji.
 *
 * @author Sebastian Krieter
 */
public class FujiSignaturesCreator {

	private static final class SignatureReference {

		private final HashMap<Integer, FOPFeatureData> ids = new HashMap<>();
		private final AbstractSignature sig;

		public SignatureReference(AbstractSignature sig) {
			this.sig = sig;
		}

		public final FOPFeatureData[] getFeatureData() {
			final FOPFeatureData[] ret = new FOPFeatureData[ids.size()];
			int i = -1;
			for (final FOPFeatureData id : ids.values()) {
				ret[++i] = id;
			}
			return ret;
		}

		public final void addID(FOPFeatureData featureData) {
			if (!ids.containsKey(featureData.getID())) {
				ids.put(featureData.getID(), featureData);
			}
		}

		public final AbstractSignature getSig() {
			return sig;
		}
	}

	private java.util.List<String> featureModulePathnames = null;

	private String getFeatureName(ASTNode<?> astNode) {
		final int featureID = astNode.featureID();

		final String featurename = featureModulePathnames.get(featureID);
		return featurename.substring(featurename.lastIndexOf(File.separator) + 1);
	}

	private final HashMap<AbstractSignature, SignatureReference> signatureSet = new HashMap<AbstractSignature, SignatureReference>();
	private final HashMap<String, AbstractSignature> signatureTable = new HashMap<String, AbstractSignature>();

	private FeatureDataConstructor featureDataConstructor = null;

	public ProjectSignatures createSignatures(IFeatureProject fp, Program ast) {
		featureModulePathnames = ast.getSPLStructure().getFeatureModulePathnames();

		final ProjectSignatures projectSignatures = new ProjectSignatures(fp.getFeatureModel());
		featureDataConstructor = new FeatureDataConstructor(projectSignatures, FeatureDataConstructor.TYPE_FOP);

		final LinkedList<TypeDecl> stack = new LinkedList<TypeDecl>();
		final LinkedList<AbstractClassSignature> roleStack = new LinkedList<AbstractClassSignature>();

		for (final Iterator<CompilationUnit> unitIter = ast.compilationUnitIterator(); unitIter.hasNext();) {
			final CompilationUnit unit = unitIter.next();
			if (unit.featureID() < 0) {
				continue;
			}
			String featurename = getFeatureName(unit);

			final List<TypeDecl> typeDeclList = unit.getTypeDeclList();
			final String pckg = unit.getPackageDecl();

			final List<ImportDecl> importList = unit.getImportDeclList();

			for (final TypeDecl rootTypeDecl : typeDeclList) {
				stack.push(rootTypeDecl);
				do {
					final TypeDecl typeDecl = stack.pop();
					String name = typeDecl.name();

					// get modifiers
					final StringBuilder classModifierSB = new StringBuilder();
					for (final Modifier modifier : typeDecl.getModifiers().getModifierList()) {
						classModifierSB.append(modifier.getID() + " ");
					}
					String modifierString = classModifierSB.toString();

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
					final FujiClassSignature curClassSig =
						(FujiClassSignature) addFeatureID(new FujiClassSignature(parent, name, modifierString, typeString, pckg, typeDecl, importList),
								projectSignatures.getFeatureID(featurename), Symbol.getLine(typeDecl.getStart()), Symbol.getLine(typeDecl.getEnd()));
					for (final ImportDecl importDecl : importList) {
						curClassSig.addImport(importDecl.toString());
					}

					for (final BodyDecl bodyDecl : typeDecl.getBodyDeclList()) {
						if (bodyDecl instanceof MethodDecl) {
							final MethodDecl method = (MethodDecl) bodyDecl;

							// get modifiers
							final StringBuilder bodyModifierSB = new StringBuilder();
							for (final Modifier modifier : method.getModifiers().getModifierList()) {
								bodyModifierSB.append(modifier.getID() + " ");
							}
							modifierString = bodyModifierSB.toString();
							name = method.name();
							final TypeDecl type = method.type();

							final List<ParameterDeclaration> parameterList = method.getParameterList();
							final List<Access> exceptionList = method.getExceptionList();

							featurename = getFeatureName(bodyDecl);
							addFeatureID(new FujiMethodSignature(curClassSig, name, modifierString, type, false, parameterList, exceptionList),
									projectSignatures.getFeatureID(featurename), Symbol.getLine(method.getStart()), Symbol.getLine(method.getEnd()));

						} else if (bodyDecl instanceof FieldDeclaration) {
							final FieldDeclaration field = (FieldDeclaration) bodyDecl;

							// get modifiers
							final StringBuilder bodyModifierSB = new StringBuilder();
							for (final Modifier modifier : field.getModifiers().getModifierList()) {
								bodyModifierSB.append(modifier.getID() + " ");
							}
							modifierString = bodyModifierSB.toString();
							name = field.name();
							final TypeDecl type = field.type();

							featurename = getFeatureName(bodyDecl);
							addFeatureID(new FujiFieldSignature(curClassSig, name, modifierString, type), projectSignatures.getFeatureID(featurename),
									Symbol.getLine(field.getStart()), Symbol.getLine(field.getEnd()));

						} else if (bodyDecl instanceof ConstructorDecl) {
							final ConstructorDecl constructor = (ConstructorDecl) bodyDecl;
							if (!constructor.isDefaultConstructor()) {
								// get modifiers
								final StringBuilder bodyModifierSB = new StringBuilder();
								for (final Modifier modifier : constructor.getModifiers().getModifierList()) {
									bodyModifierSB.append(modifier.getID() + " ");
								}
								modifierString = bodyModifierSB.toString();
								name = constructor.name();
								final TypeDecl type = constructor.type();

								final List<ParameterDeclaration> parameterList = constructor.getParameterList();
								final List<Access> exceptionList = constructor.getExceptionList();

								featurename = getFeatureName(bodyDecl);
								addFeatureID(new FujiMethodSignature(curClassSig, name, modifierString, type, true, parameterList, exceptionList),
										projectSignatures.getFeatureID(featurename), Symbol.getLine(constructor.getStart()),
										Symbol.getLine(constructor.getEnd()));
							}

						} else if (bodyDecl instanceof MemberClassDecl) {
							stack.push(((MemberClassDecl) bodyDecl).getClassDecl());
							roleStack.push(curClassSig);
						} else if (bodyDecl instanceof MemberInterfaceDecl) {
							stack.push(((MemberInterfaceDecl) bodyDecl).getInterfaceDecl());
							roleStack.push(curClassSig);
						}

					}
				} while (!stack.isEmpty());
			}
		}

		final AbstractSignature[] sigArray = new AbstractSignature[signatureSet.size()];
		int i = -1;

		for (final SignatureReference sigRef : signatureSet.values()) {
			final AbstractSignature sig = sigRef.getSig();
			sig.setFeatureData(sigRef.getFeatureData());
			sigArray[++i] = sig;
		}

		projectSignatures.setSignatureArray(sigArray);

		return projectSignatures;
	}

	private AbstractSignature addFeatureID(AbstractSignature sig, int featureID, int startLine, int endLine) {
		SignatureReference sigRef = signatureSet.get(sig);
		if (sigRef == null) {
			sigRef = new SignatureReference(sig);
			signatureSet.put(sig, sigRef);
			signatureTable.put(sig.getFullName(), sig);
		}
		sigRef.addID((FOPFeatureData) featureDataConstructor.create(featureID, startLine, endLine));
		return sigRef.getSig();
	}

	public void attachJavadocComments(ProjectSignatures projectSignatures, FSTModel fst) {
		if (fst == null) {
			FeatureHouseCorePlugin.getDefault().logInfo("Kein FSTModel!");
		} else {
			for (final FSTFeature fstFeature : fst.getFeatures()) {
				final int id = projectSignatures.getFeatureID(fstFeature.getName());

				for (final FSTRole fstRole : fstFeature.getRoles()) {
					final FSTClassFragment classFragment = fstRole.getClassFragment();
					String fullName;
					if (classFragment.getPackage() == null) {
						fullName = "." + classFragment.getName();
					} else {
						fullName = classFragment.getName();
						fullName = fullName.replace('/', '.');
					}
					if (fullName.endsWith(".java")) {
						fullName = fullName.substring(0, fullName.length() - ".java".length());
					}
					copyComment_rec(classFragment, id, fullName);
				}
			}
		}
	}

	private void copyComment(IRoleElement element, int id, String fullName) {
		if (fullName == null) {
			return;
		}
		final AbstractSignature sig = signatureTable.get(fullName);

		if (sig != null) {
			final FOPFeatureData[] ids = (FOPFeatureData[]) sig.getFeatureData();
			for (int j = 0; j < ids.length; j++) {
				final FOPFeatureData featureData = ids[j];
				if (featureData.getID() == id) {
					featureData.setComment(element.getJavaDocComment());
					break;
				}
			}
		}
	}

	private void copyComment_rec(FSTClassFragment classFragment, int id, String fullName) {
		copyComment(classFragment, id, fullName);
		for (final FSTField field : classFragment.getFields()) {
			copyComment(field, id, fullName + "." + field.getName());
		}
		for (final FSTMethod method : classFragment.getMethods()) {
			copyComment(method, id, fullName + "." + method.getName());
		}
		for (final FSTClassFragment innerClasses : classFragment.getInnerClasses()) {
			copyComment_rec(innerClasses, id, fullName + "." + innerClasses.getName());
		}
	}
}
