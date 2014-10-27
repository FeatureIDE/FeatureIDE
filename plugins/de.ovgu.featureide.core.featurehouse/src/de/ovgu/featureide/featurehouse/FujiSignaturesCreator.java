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
package de.ovgu.featureide.featurehouse;

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
import de.ovgu.featureide.core.fstmodel.RoleElement;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.abstr.AbstractClassSignature;
import de.ovgu.featureide.core.signature.abstr.AbstractSignature;
import de.ovgu.featureide.core.signature.abstr.AbstractSignature.FeatureData;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiClassSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiFieldSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;

/**
 * Loads the signatures from Fuji.
 * 
 * @author Sebastian Krieter
 */
public class FujiSignaturesCreator {
	
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

	private java.util.List<String> featureModulePathnames = null;
	
	private String getFeatureName(ASTNode<?> astNode) {
		int featureID = astNode.featureID();

		String featurename = featureModulePathnames.get(featureID);
		return featurename.substring(featurename.lastIndexOf('\\') + 1);
	}

	private final HashMap<AbstractSignature, SignatureReference> signatureSet = new HashMap<AbstractSignature, SignatureReference>();
	private final HashMap<String, AbstractSignature> signatureTable = new HashMap<String, AbstractSignature>();
	
	public ProjectSignatures createSignatures(IFeatureProject fp, Program ast) {
		featureModulePathnames = ast.getSPLStructure().getFeatureModulePathnames();
		
		final ProjectSignatures projectSignatures = new ProjectSignatures(fp.getFeatureModel());
		
		LinkedList<TypeDecl> stack = new LinkedList<TypeDecl>();
		LinkedList<AbstractClassSignature> roleStack = new LinkedList<AbstractClassSignature>();

		for (@SuppressWarnings("unchecked") Iterator<CompilationUnit> unitIter = ast.compilationUnitIterator(); unitIter.hasNext();) {
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
									projectSignatures.getFeatureID(featurename), Symbol.getLine(typeDecl.getStart()));
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
									projectSignatures.getFeatureID(featurename), Symbol.getLine(method.getStart()));

						} else if (bodyDecl instanceof FieldDeclaration) {
							FieldDeclaration field = (FieldDeclaration) bodyDecl;

							modifierString = field.getModifiers().toString();
							name = field.name();
							TypeDecl type = field.type();

							featurename = getFeatureName(bodyDecl);
							addFeatureID(new FujiFieldSignature(curClassSig,
									name, modifierString, type),
									projectSignatures.getFeatureID(featurename), Symbol.getLine(field.getStart()));

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
										projectSignatures.getFeatureID(featurename), Symbol.getLine(constructor.getStart()));
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
	
	private AbstractSignature addFeatureID(AbstractSignature sig, int featureID, int line) {
		SignatureReference sigRef = signatureSet.get(sig);
		if (sigRef == null) {
			sigRef = new SignatureReference(sig);
			signatureSet.put(sig, sigRef);
			signatureTable.put(sig.getFullName(), sig);
		}
		sigRef.addID(new FeatureData(featureID, line));
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
	
	private void copyComment(RoleElement element, int id, String fullName) {
		if (fullName == null) {
			return;
		}
		AbstractSignature sig = signatureTable.get(fullName);
		
		if (sig != null) {
			final FeatureData[] ids = sig.getFeatureData();
			for (int j = 0; j < ids.length; j++) {
				FeatureData featureData = ids[j];
				if (featureData.getId() == id) {
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
