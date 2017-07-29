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
import de.ovgu.featureide.core.signature.base.SignaturePosition;
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
			FOPFeatureData[] ret = new FOPFeatureData[ids.size()];
			int i = -1;
			for (FOPFeatureData id : ids.values()) {
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
		
		public void setAbsoluteFilePath(int featureID, String absoluteFilePath) {
			if (ids.containsKey(featureID)) {
				ids.get(featureID).setAbsoluteFilePath(absoluteFilePath);
			}
		}

	}

	private java.util.List<String> featureModulePathnames = null;

	private String getFeatureName(ASTNode<?> astNode) {
		int featureID = astNode.featureID();

		String featurename = featureModulePathnames.get(featureID);
		return featurename.substring(featurename.lastIndexOf(File.separator) + 1);
	}

	private final HashMap<AbstractSignature, SignatureReference> signatureSet = new HashMap<AbstractSignature, SignatureReference>();
	private final HashMap<String, AbstractSignature> signatureTable = new HashMap<String, AbstractSignature>();

	private FeatureDataConstructor featureDataConstructor = null;

	public ProjectSignatures createSignatures(IFeatureProject fp, Program ast) {
		featureModulePathnames = ast.getSPLStructure().getFeatureModulePathnames();

		final ProjectSignatures projectSignatures = new ProjectSignatures(fp.getFeatureModel());
		featureDataConstructor = new FeatureDataConstructor(projectSignatures, FeatureDataConstructor.TYPE_FOP);

		LinkedList<TypeDecl> stack = new LinkedList<TypeDecl>();
		LinkedList<AbstractClassSignature> roleStack = new LinkedList<AbstractClassSignature>();

		for (Iterator<CompilationUnit> unitIter = ast.compilationUnitIterator(); unitIter.hasNext();) {
			CompilationUnit unit = unitIter.next();
			if (unit.featureID() < 0) {
				continue;
			}
			String featurename = getFeatureName(unit);
			
			String absoluteFilePath = unit.relativeName();

			List<TypeDecl> typeDeclList = unit.getTypeDeclList();
			String pckg = unit.getPackageDecl();

			List<ImportDecl> importList = unit.getImportDeclList();

			for (TypeDecl rootTypeDecl : typeDeclList) {
				stack.push(rootTypeDecl);
				do {
					TypeDecl typeDecl = stack.pop();
					String name = typeDecl.name();

					// get modifiers
					StringBuilder classModifierSB = new StringBuilder();
					for (Modifier modifier : typeDecl.getModifiers().getModifierList()) {
						classModifierSB.append(modifier.getID() + " ");
					}
					String modifierString = classModifierSB.toString();

					String typeString = null;
					if (typeDecl instanceof ClassDecl) {
						typeString = AbstractClassSignature.TYPE_CLASS;
					} else if (typeDecl instanceof InterfaceDecl) {
						typeString = AbstractClassSignature.TYPE_INTERFACE;
					}

					AbstractClassSignature parent = null;
					if (!roleStack.isEmpty()) {
						parent = roleStack.pop();
					}
					featurename = getFeatureName(typeDecl);
					FujiClassSignature curClassSig = (FujiClassSignature) addFeatureID(
<<<<<<< HEAD
							new FujiClassSignature(parent, name, modifierString, typeString, pckg, typeDecl, importList),
							projectSignatures.getFeatureID(featurename), Symbol.getLine(typeDecl.getStart()), Symbol.getLine(typeDecl.getEnd()));
=======
							new FujiClassSignature(parent, name,
									modifierString, typeString, pckg, typeDecl,
									importList),
									projectSignatures.getFeatureID(featurename), 
									typeDecl.getStart(), typeDecl.getEnd(), typeDecl.IDstart, typeDecl.IDend, 
									absoluteFilePath);
>>>>>>> refs/remotes/FeatureIDE/fop-pullup-codeclones
					for (ImportDecl importDecl : importList) {
						curClassSig.addImport(importDecl.toString());
					}

					for (BodyDecl bodyDecl : typeDecl.getBodyDeclList()) {
						if (bodyDecl instanceof MethodDecl) {
							MethodDecl method = (MethodDecl) bodyDecl;

							// get modifiers
							StringBuilder bodyModifierSB = new StringBuilder();
							for (Modifier modifier : method.getModifiers().getModifierList()) {
								bodyModifierSB.append(modifier.getID() + " ");
							}
							modifierString = bodyModifierSB.toString();
							name = method.name();
							TypeDecl type = method.type();

							List<ParameterDeclaration> parameterList = method.getParameterList();
							List<Access> exceptionList = method.getExceptionList();

							featurename = getFeatureName(bodyDecl);
<<<<<<< HEAD
							addFeatureID(new FujiMethodSignature(curClassSig, name, modifierString, type, false, parameterList, exceptionList),
									projectSignatures.getFeatureID(featurename), Symbol.getLine(method.getStart()), Symbol.getLine(method.getEnd()));
=======
							addFeatureID(new FujiMethodSignature(curClassSig,
									name, modifierString, type, false,
									parameterList, exceptionList),
									projectSignatures.getFeatureID(featurename), 
									method.getStart(), method.getEnd(), method.IDstart, method.IDend, 
									absoluteFilePath);
>>>>>>> refs/remotes/FeatureIDE/fop-pullup-codeclones

						} else if (bodyDecl instanceof FieldDeclaration) {
							FieldDeclaration field = (FieldDeclaration) bodyDecl;

							// get modifiers
							StringBuilder bodyModifierSB = new StringBuilder();
							for (Modifier modifier : field.getModifiers().getModifierList()) {
								bodyModifierSB.append(modifier.getID() + " ");
							}
							modifierString = bodyModifierSB.toString();
							name = field.name();
							TypeDecl type = field.type();

							featurename = getFeatureName(bodyDecl);
<<<<<<< HEAD
							addFeatureID(new FujiFieldSignature(curClassSig, name, modifierString, type), projectSignatures.getFeatureID(featurename),
									Symbol.getLine(field.getStart()), Symbol.getLine(field.getEnd()));
=======
							addFeatureID(new FujiFieldSignature(curClassSig,
									name, modifierString, type, field),
									projectSignatures.getFeatureID(featurename), 
									field.getStart(), field.getEnd(), field.IDstart, field.IDend, 
									absoluteFilePath);
>>>>>>> refs/remotes/FeatureIDE/fop-pullup-codeclones

						} else if (bodyDecl instanceof ConstructorDecl) {
							ConstructorDecl constructor = (ConstructorDecl) bodyDecl;
							if (!constructor.isDefaultConstructor()) {
								// get modifiers
								StringBuilder bodyModifierSB = new StringBuilder();
								for (Modifier modifier : constructor.getModifiers().getModifierList()) {
									bodyModifierSB.append(modifier.getID() + " ");
								}
								modifierString = bodyModifierSB.toString();
								name = constructor.name();
								TypeDecl type = constructor.type();

								List<ParameterDeclaration> parameterList = constructor.getParameterList();
								List<Access> exceptionList = constructor.getExceptionList();

								featurename = getFeatureName(bodyDecl);
<<<<<<< HEAD
								addFeatureID(new FujiMethodSignature(curClassSig, name, modifierString, type, true, parameterList, exceptionList),
										projectSignatures.getFeatureID(featurename), Symbol.getLine(constructor.getStart()),
										Symbol.getLine(constructor.getEnd()));
=======
								addFeatureID(new FujiMethodSignature(
										curClassSig, name, modifierString,
										type, true, parameterList,
										exceptionList),
										projectSignatures.getFeatureID(featurename), 
										constructor.getStart(), constructor.getEnd(), constructor.IDstart, constructor.IDend, 
										absoluteFilePath);
>>>>>>> refs/remotes/FeatureIDE/fop-pullup-codeclones
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

		for (SignatureReference sigRef : signatureSet.values()) {
			AbstractSignature sig = sigRef.getSig();
			sig.setFeatureData(sigRef.getFeatureData());
			sigArray[++i] = sig;
		}

		projectSignatures.setSignatureArray(sigArray);

		return projectSignatures;
	}
<<<<<<< HEAD

	private AbstractSignature addFeatureID(AbstractSignature sig, int featureID, int startLine, int endLine) {
=======
	
	private AbstractSignature addFeatureID(AbstractSignature sig, int featureID, int start, int end, int identifierStart, int identifierEnd, String absoluteFilePath) {
>>>>>>> refs/remotes/FeatureIDE/fop-pullup-codeclones
		SignatureReference sigRef = signatureSet.get(sig);
		if (sigRef == null) {
			sigRef = new SignatureReference(sig);
			signatureSet.put(sig, sigRef);
			signatureTable.put(sig.getFullName(), sig);
		}
		SignaturePosition position = new SignaturePosition(Symbol.getLine(start), Symbol.getLine(end), Symbol.getColumn(start), Symbol.getColumn(end),
				Symbol.getColumn(identifierStart), Symbol.getColumn(identifierEnd));
		sigRef.addID((FOPFeatureData) featureDataConstructor.create(featureID, position));
		sigRef.setAbsoluteFilePath(featureID, absoluteFilePath);
		return sigRef.getSig();
	}

	public void attachJavadocComments(ProjectSignatures projectSignatures, FSTModel fst) {
		if (fst == null) {
			FeatureHouseCorePlugin.getDefault().logInfo("Kein FSTModel!");
		} else {
			for (FSTFeature fstFeature : fst.getFeatures()) {
				final int id = projectSignatures.getFeatureID(fstFeature.getName());

				for (FSTRole fstRole : fstFeature.getRoles()) {
					FSTClassFragment classFragment = fstRole.getClassFragment();
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
		AbstractSignature sig = signatureTable.get(fullName);

		if (sig != null) {
			final FOPFeatureData[] ids = (FOPFeatureData[]) sig.getFeatureData();
			for (int j = 0; j < ids.length; j++) {
				FOPFeatureData featureData = ids[j];
				if (featureData.getID() == id) {
					featureData.setComment(element.getJavaDocComment());
					break;
				}
			}
		}
	}

	private void copyComment_rec(FSTClassFragment classFragment, int id, String fullName) {
		copyComment(classFragment, id, fullName);
		for (FSTField field : classFragment.getFields()) {
			copyComment(field, id, fullName + "." + field.getName());
		}
		for (FSTMethod method : classFragment.getMethods()) {
			copyComment(method, id, fullName + "." + method.getName());
		}
		for (FSTClassFragment innerClasses : classFragment.getInnerClasses()) {
			copyComment_rec(innerClasses, id, fullName + "." + innerClasses.getName());
		}
	}
}
