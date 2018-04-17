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

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Loads the signatures from Fuji.
 *
 * @author Sebastian Krieter
 * @author Marcus Pinnecke
 */
//@SuppressWarnings(RESTRICTION)
public class ExtendedFujiSignaturesJob implements LongRunningMethod<ProjectSignatures> {

//	private static final class SignatureReference {
//		private final HashMap<Integer, FOPFeatureData> ids = new HashMap<>();
//		private final AbstractSignature sig;
//
//		public SignatureReference(AbstractSignature sig) {
//			this.sig = sig;
//		}
//
//		public final FOPFeatureData[] getFeatureData() {
//			FOPFeatureData[] ret = new FOPFeatureData[ids.size()];
//			int i = -1;
//			for (FOPFeatureData id : ids.values()) {
//				ret[++i] = id;
//			}
//			return ret;
//		}
//
//		public final void addID(FOPFeatureData featureData) {
//			if (!ids.containsKey(featureData.getID())) {
//				ids.put(featureData.getID(), featureData);
//			}
//		}
//
//		public final AbstractSignature getSig() {
//			return sig;
//		}
//	}

	public static final class SignatureMethodAccess {

		private final int featureID;
		private final AbstractSignature absSig;

		public int getFeatureID() {
			return featureID;
		}

		public AbstractSignature getAbsSig() {
			return absSig;
		}

		@Override
		public boolean equals(Object arg0) {
			if (arg0 == this) {
				return true;
			}
			if (!(arg0 instanceof SignatureMethodAccess)) {
				return false;
			}
			final SignatureMethodAccess comp = (SignatureMethodAccess) arg0;
			if ((featureID != comp.featureID) || !absSig.equals(comp.absSig)) {
				return false;
			}
			return true;
		}

		@Override
		public int hashCode() {
			int hashCode = featureID;
			hashCode = (37 * hashCode) + absSig.hashCode();
			return hashCode;
		}

		@Override
		public String toString() {
			return featureID + "; " + absSig.toString();
		}

		public SignatureMethodAccess(int featureID, AbstractSignature absSig) {
			this.featureID = featureID;
			this.absSig = absSig;
		}
	}

//	private static class ExtendedSignature {
//
//		private final AbstractSignature sig;
//		private final int featureID;
//
//		public ExtendedSignature(AbstractSignature sig, int featureID) {
//			this.sig = sig;
//			this.featureID = featureID;
//		}
//
//		@Override
//		public int hashCode() {
//			return (37 * featureID) + sig.hashCode();
//		}
//
//		@Override
//		public boolean equals(Object arg0) {
//			if (arg0 == this) {
//				return true;
//			}
//			if (!(arg0 instanceof ExtendedSignature)) {
//				return false;
//			}
//			ExtendedSignature comp = (ExtendedSignature) arg0;
//			if (comp.featureID == this.featureID &&
//					comp.sig.equals(this.sig)) {
//				return false;
//			}
//			return true;
//		}
//
//		@Override
//		public String toString() {
//			return this.featureID + " - " + this.sig.getFullName();
//		}
//
//
//	}

	private final IFeatureProject featureProject;
	private final ProjectSignatures projectSignatures;
//	private final FeatureDataConstructor featureDataConstructor;
//
//	private final HashMap<AbstractSignature, SignatureReference> signatureSet = new HashMap<AbstractSignature, SignatureReference>();
//	private final HashMap<String, AbstractSignature> signatureTable = new HashMap<String, AbstractSignature>();
//
//	private final HashMap<BodyDecl, java.util.List<ExtendedSignature>> bodyMap = new HashMap<BodyDecl, java.util.List<ExtendedSignature>>();
//	private final ArrayList<ExtendedSignature> originalList = new ArrayList<ExtendedSignature>();
//	private final Hashtable<ExtendedSignature, ClassDecl> nonPrimitveTypesTable = new Hashtable<ExtendedSignature, ClassDecl>();

	public ProjectSignatures getProjectSignatures() {
		return projectSignatures;
	}

	public ExtendedFujiSignaturesJob(IFeatureProject featureProject) {
		this.featureProject = featureProject;
		projectSignatures = new ProjectSignatures(this.featureProject.getFeatureModel());
//		this.featureDataConstructor = new FeatureDataConstructor(projectSignatures, FeatureDataConstructor.TYPE_FOP);
	}

//	private AbstractSignature addFeatureID(AbstractSignature sig, int featureID, int startLine, int endLine) {
//		SignatureReference sigRef = signatureSet.get(sig);
//		if (sigRef == null) {
//			sigRef = new SignatureReference(sig);
//			signatureSet.put(sig, sigRef);
//			signatureTable.put(sig.getFullName(), sig);
//		}
//		sigRef.addID((FOPFeatureData) featureDataConstructor.create(featureID, startLine, endLine));
//		return sigRef.getSig();
//	}

//	private static String getClassPaths(IFeatureProject featureProject) {
//		final StringBuilder classpath = new StringBuilder();
//		String sep = System.getProperty("path.separator");
//		try {
//			JavaProject proj = new JavaProject(featureProject.getProject(), null);
//			IJavaElement[] elements = proj.getChildren();
//			for (IJavaElement e : elements) {
//				String path = e.getPath().toOSString();
//				if (path.contains(":")) {
//					classpath.append(sep);
//					classpath.append(path);
//					continue;
//				}
//				IResource resource = e.getResource();
//				if (resource != null && "jar".equals(resource.getFileExtension())) {
//					classpath.append(sep);
//					classpath.append(resource.getRawLocation().toOSString());
//				}
//			}
//		} catch (JavaModelException e) {
//
//		}
//		return classpath.length() > 0 ? classpath.substring(1) : classpath.toString();
//	}
//
//	private java.util.List<String> featureModulePathnames = null;
//
//	@SuppressWarnings("rawtypes")
//	private String getFeatureName(ASTNode astNode) {
//		int featureID = astNode.featureID();
//
//		String featurename = featureModulePathnames.get(featureID);
//		return featurename.substring(featurename.lastIndexOf('\\') + 1);
//	}

	@Override
	public ProjectSignatures execute(IMonitor monitor) throws Exception {
//		IFeatureModel fm = featureProject.getFeatureModel();
//		fm.getAnalyser().setDependencies();
//
//		String sourcePath = featureProject.getSourcePath();
//		String[] fujiOptions = new String[] { "-" + Main.OptionName.CLASSPATH, getClassPaths(featureProject), "-" + Main.OptionName.PROG_MODE,
//				"-" + Main.OptionName.COMPOSTION_STRATEGY, Main.OptionName.COMPOSTION_STRATEGY_ARG_FAMILY // "-typechecker",
//				, "-" + Main.OptionName.BASEDIR, sourcePath };
//		SPLStructure spl = null;
//		Program ast;
//		try {
		throw new UnsupportedOperationException("Fuji is currently not supported.");
//			Main fuji = new Main(fujiOptions, new FeatureModel(fm), FeatureUtils.extractConcreteFeaturesAsStringList(fm), FeatureUtils.CHARSQUENCE_TO_STRING);
//
//			Composition composition = fuji.getComposition(fuji);
//			ast = composition.composeAST();
//			fuji.typecheckAST(ast);
//			spl = fuji.getSPLStructure();
//			featureModulePathnames = spl.getFeatureModulePathnames();
//		} catch (RuntimeException e) {
//			throw e;
//		} catch (Exception e) {
//			FeatureHouseCorePlugin.getDefault().logError(e);
//			return false;
//		}

//		createSignatures(featureProject, ast);
//
//		FeatureHouseCorePlugin.getDefault().logInfo(FUJI_SIGNATURES_LOADED_);
//		return true;
	}

//	@SuppressWarnings("unchecked")
//	private void createSignatures(IFeatureProject fp, Program ast) {
//		int count = 0;
//		Iterator<CompilationUnit> unitIter = ast.compilationUnitIterator();
//		while (unitIter.hasNext()) {
//			if (unitIter.next().featureID() >= 0) {
//				++count;
//			}
//		}
//		workMonitor.setMaxAbsoluteWork(2 * count);
//
//		LinkedList<TypeDecl> stack = new LinkedList<TypeDecl>();
//		LinkedList<AbstractClassSignature> roleStack = new LinkedList<AbstractClassSignature>();
//
//		unitIter = ast.compilationUnitIterator();
//		while (unitIter.hasNext()) {
//			CompilationUnit unit = unitIter.next();
//			if (unit.featureID() < 0) {
//				continue;
//			}
//			String featurename = getFeatureName(unit);
//
//			List<TypeDecl> typeDeclList = unit.getTypeDeclList();
//			String pckg = unit.getPackageDecl();
//
//			List<ImportDecl> importList = unit.getImportDeclList();
//
//			for (TypeDecl rootTypeDecl : typeDeclList) {
//				stack.push(rootTypeDecl);
//				do {
//					TypeDecl typeDecl = stack.pop();
//					String name = typeDecl.name();
//					String modifierString = typeDecl.getModifiers().toString();
//					String typeString = null;
//
//					if (typeDecl instanceof ClassDecl) {
//						typeString = "class";
//					} else if (typeDecl instanceof InterfaceDecl) {
//						typeString = "interface";
//					}
//
//					AbstractClassSignature parent = null;
//					if (!roleStack.isEmpty()) {
//						parent = roleStack.pop();
//					}
//					featurename = getFeatureName(typeDecl);
//					int featureID = projectSignatures.getFeatureID(featurename);
//
//					FujiClassSignature curClassSig = (FujiClassSignature) addFeatureID(new FujiClassSignature(parent, name, modifierString,
//							typeString, pckg, typeDecl, importList), featureID, Symbol.getLine(typeDecl.getStart()), Symbol.getLine(typeDecl.getEnd()));
//					for (ImportDecl importDecl : importList) {
//						curClassSig.addImport(importDecl.toString());
//					}
//
//					for (BodyDecl bodyDecl : typeDecl.getBodyDeclList()) {
//						typeDecl.getModifiers();
//						if (bodyDecl instanceof MethodDecl) {
//							MethodDecl method = (MethodDecl) bodyDecl;
//
//							modifierString = method.getModifiers().toString();
//							name = method.name();
//
//							TypeDecl type = method.type();
//
//							List<ParameterDeclaration> parameterList = method.getParameterList();
//							List<Access> exceptionList = method.getExceptionList();
//
//							featurename = getFeatureName(bodyDecl);
//							featureID = projectSignatures.getFeatureID(featurename);
//
//							AbstractSignature methAbs = addFeatureID(new FujiMethodSignature(curClassSig, name, modifierString, type,
//									false, parameterList, exceptionList), featureID, Symbol.getLine(method.getStart()), Symbol.getLine(method.getEnd()));
//							findMethodAccesses(method, methAbs, featureID);
//						} else if (bodyDecl instanceof FieldDeclaration) {
//							FieldDeclaration field = (FieldDeclaration) bodyDecl;
//
//							modifierString = field.getModifiers().toString();
//							name = field.name();
//							TypeDecl type = field.type();
//
//							featurename = getFeatureName(bodyDecl);
//							featureID = projectSignatures.getFeatureID(featurename);
//
//							addFeatureID(new FujiFieldSignature(curClassSig, name, modifierString, type), featureID,
//									Symbol.getLine(field.getStart()), Symbol.getLine(field.getEnd()));
//
//						} else if (bodyDecl instanceof ConstructorDecl) {
//							ConstructorDecl constructor = (ConstructorDecl) bodyDecl;
//							if (!constructor.isDefaultConstructor()) {
//								modifierString = constructor.getModifiers().toString();
//								name = constructor.name();
//
//								TypeDecl type = constructor.type();
//
//								List<ParameterDeclaration> parameterList = constructor.getParameterList();
//								List<Access> exceptionList = constructor.getExceptionList();
//
//								featurename = getFeatureName(bodyDecl);
//								featureID = projectSignatures.getFeatureID(featurename);
//
//								AbstractSignature constrAbs = addFeatureID(new FujiMethodSignature(curClassSig, name, modifierString, type,
//										true, parameterList, exceptionList), featureID, Symbol.getLine(constructor.getStart()), Symbol.getLine(constructor.getEnd()));
//								findMethodAccesses(constructor, constrAbs, featureID);
//							}
//
//						} else if (bodyDecl instanceof MemberClassDecl) {
//							stack.push(((MemberClassDecl) bodyDecl).getClassDecl());
//							roleStack.push(curClassSig);
//						} else if (bodyDecl instanceof MemberInterfaceDecl) {
//							stack.push(((MemberInterfaceDecl) bodyDecl).getInterfaceDecl());
//							roleStack.push(curClassSig);
//						}
//					}
//				} while (!stack.isEmpty());
//			}
//			workMonitor.worked();
//		}
//
//		final AbstractSignature[] sigArray = new AbstractSignature[signatureSet.size()];
//		int i = -1;
//
//		for (SignatureReference sigRef : signatureSet.values()) {
//			AbstractSignature sig = sigRef.getSig();
//			sig.setFeatureData(sigRef.getFeatureData());
//			sigArray[++i] = sig;
//		}
//
//		unitIter = ast.compilationUnitIterator();
//		while (unitIter.hasNext()) {
//			CompilationUnit unit = unitIter.next();
//			if (unit.featureID() < 0) {
//				continue;
//			}
//
//			List<TypeDecl> typeDeclList = unit.getTypeDeclList();
//			String pckg = unit.getPackageDecl();
//
//			List<ImportDecl> importList = unit.getImportDeclList();
//
//			for (TypeDecl rootTypeDecl : typeDeclList) {
//				stack.push(rootTypeDecl);
//				do {
//					TypeDecl typeDecl = stack.pop();
//					String name = typeDecl.name();
//					String modifierString = typeDecl.getModifiers().toString();
//					String typeString = null;
//
//					if (typeDecl instanceof ClassDecl) {
//						typeString = "class";
//					} else if (typeDecl instanceof InterfaceDecl) {
//						typeString = "interface";
//					}
//
//					AbstractClassSignature parent = null;
//					if (!roleStack.isEmpty()) {
//						parent = roleStack.pop();
//					}
//					FujiClassSignature curClassSig = (FujiClassSignature) signatureSet.get(new FujiClassSignature(parent, name,
//							modifierString, typeString, pckg, typeDecl, importList)).sig;
//
//					for (BodyDecl bodyDecl : typeDecl.getBodyDeclList()) {
//						typeDecl.getModifiers();
//						java.util.List<ExtendedSignature> accessingSignatures = bodyMap.remove(bodyDecl);
//						if (accessingSignatures != null) {
//							SignatureReference sigRef = null;
//							if (bodyDecl instanceof MethodDecl) {
//								MethodDecl method = (MethodDecl) bodyDecl;
//								modifierString = method.getModifiers().toString();
//								name = method.name();
//
//								TypeDecl type = method.type();
//
//								List<ParameterDeclaration> parameterList = method.getParameterList();
//								List<Access> exceptionList = method.getExceptionList();
//								sigRef = signatureSet.get(new FujiMethodSignature(curClassSig, name, modifierString,
//										type, false, parameterList, exceptionList));
//							} else if (bodyDecl instanceof FieldDeclaration) {
//								FieldDeclaration field = (FieldDeclaration) bodyDecl;
//
//								modifierString = field.getModifiers().toString();
//								name = field.name();
//								TypeDecl type = field.type();
//
//								sigRef = signatureSet.get(new FujiFieldSignature(curClassSig, name, modifierString, type));
//							} else if (bodyDecl instanceof ConstructorDecl) {
//								ConstructorDecl constructor = (ConstructorDecl) bodyDecl;
//								if (!constructor.isDefaultConstructor()) {
//									modifierString = constructor.getModifiers().toString();
//									name = constructor.name();
//									TypeDecl type = constructor.type();
//
//									List<ParameterDeclaration> parameterList = constructor.getParameterList();
//									List<Access> exceptionList = constructor.getExceptionList();
//
//									sigRef = signatureSet.get(new FujiMethodSignature(curClassSig, name, modifierString, type,
//											true, parameterList, exceptionList));
//								}
//							}
//							if (sigRef != null) {
//								for (ExtendedSignature absSig : accessingSignatures) {
//									final FOPFeatureData[] featureData = (FOPFeatureData[]) absSig.sig.getFeatureData();
//									for (int j = 0; j < featureData.length; j++) {
//										if (featureData[j].getID() == absSig.featureID) {
//											featureData[j].addCalledSignature(sigRef.sig);
//											break;
//										}
//									}
//								}
//							}
//						} else if (bodyDecl instanceof MemberClassDecl) {
//							stack.push(((MemberClassDecl) bodyDecl).getClassDecl());
//							roleStack.push(curClassSig);
//						}
//					}
//				} while (!stack.isEmpty());
//			}
//			workMonitor.worked();
//		}
//		for (ExtendedSignature extSig : originalList) {
//			final FOPFeatureData[] featureData = (FOPFeatureData[]) extSig.sig.getFeatureData();
//			for (int j = 0; j < featureData.length; j++) {
//				if (featureData[j].getID() == extSig.featureID) {
//					featureData[j].setUsesOriginal(true);
//					break;
//				}
//			}
//
//		}
//
//		for (Entry<ExtendedSignature, ClassDecl> extSig : nonPrimitveTypesTable.entrySet()) {
//			final FOPFeatureData[] featureData = (FOPFeatureData[]) extSig.getKey().sig.getFeatureData();
//			for (int j = 0; j < featureData.length; j++) {
//				if (featureData[j].getID() == extSig.getKey().featureID) {
//					featureData[j].addUsedNonPrimitveType(extSig.getValue().name());
//					break;
//				}
//			}
//		}
//
//		for (java.util.List<ExtendedSignature> value  : bodyMap.values()) {
//			for (ExtendedSignature absSig : value) {
//				if (absSig.sig instanceof AbstractMethodSignature) {
//					AbstractMethodSignature methSig = (AbstractMethodSignature) absSig.sig;
//					if (methSig.isConstructor()) {
//						continue;
//					}
//				}
//				final FOPFeatureData[] featureData = (FOPFeatureData[]) absSig.sig.getFeatureData();
//				for (int j = 0; j < featureData.length; j++) {
//					if (featureData[j].getID() == absSig.featureID) {
//						featureData[j].setUsesExternMethods(true);
//						break;
//					}
//				}
//			}
//		}
//
//		fp.getComposer().buildFSTModel();
//		FSTModel fst = fp.getFSTModel();
//
//		if (fst == null) {
//			FeatureHouseCorePlugin.getDefault().logInfo(NO_FSTMODEL_PROVIDED_);
//		} else {
//			for (FSTFeature fstFeature : fst.getFeatures()) {
//				final int id = projectSignatures.getFeatureID(fstFeature.getName());
//
//				for (FSTRole fstRole : fstFeature.getRoles()) {
//					FSTClassFragment classFragment = fstRole.getClassFragment();
//					String fullName = (classFragment.getPackage() == null ? "" : classFragment.getPackage()) + "."
//							+ classFragment.getName();
//					if (fullName.endsWith(".java")) {
//						fullName = fullName.substring(0, fullName.length() - ".java".length());
//					}
//					copyComment_rec(classFragment, id, fullName);
//				}
//			}
//		}
//
//		projectSignatures.setSignatureArray(sigArray);
//		featureProject.getFSTModel().setProjectSignatures(projectSignatures);
//	}

//	private void findMethodAccesses(ASTNode<?> stmt, AbstractSignature methAbs, int featureID) {
//		if (stmt == null) {
//			return;
//		}
//
//		if (stmt instanceof MethodAccess) {
//			if ("original".equals(((MethodAccess) stmt).name())) {
//				originalList.add(new ExtendedSignature(methAbs, featureID));
//			} else {
//				putAccess(((MethodAccess) stmt).decl(), methAbs, featureID);
//			}
//			for (int i = 0; i < stmt.getNumChildNoTransform(); i++) {
//				findMethodAccesses(stmt.getChildNoTransform(i), methAbs, featureID);
//			}
//		} else if (stmt instanceof ConstructorAccess) {
//			putAccess(((ConstructorAccess) stmt).decl(), methAbs, featureID);
//		} else if (stmt instanceof VarAccess) {
//			Iterator<?> declIt = ((VarAccess) stmt).decls().iterator();
//			while (declIt.hasNext()) {
//				Object fieldDecl = declIt.next();
//				if (fieldDecl instanceof FieldDeclaration) {
//					putAccess((FieldDeclaration) fieldDecl, methAbs, featureID);
//					break;
//				}
//			}
//		} else if (stmt instanceof ClassInstanceExpr) {
//			Iterator<?> iterator = (((ClassInstanceExpr) stmt).decls().iterator());
//			while (iterator.hasNext()) {
//				Object cur = iterator.next();
//				if (cur instanceof ConstructorDecl) {
//					putAccess((ConstructorDecl) cur, methAbs, featureID);
//					break;
//				}
//			}
//		} else if (stmt instanceof TypeAccess){
//			Iterator<?> iterator = (((TypeAccess) stmt).decls().iterator());
//			while (iterator.hasNext()) {
//				Object cur = iterator.next();
//				if (cur instanceof ClassDecl) {
//					nonPrimitveTypesTable.put(new ExtendedSignature(methAbs, featureID), (ClassDecl) cur);
//					break;
//				}
//			}
//		} else {
//			for (int i = 0; i < stmt.getNumChildNoTransform(); i++) {
//				findMethodAccesses(stmt.getChildNoTransform(i), methAbs, featureID);
//			}
//		}
//	}
//
//	private void putAccess(BodyDecl typeDecl, AbstractSignature methAbs, int featureID) {
//		java.util.List<ExtendedSignature> signatureList = bodyMap.get(typeDecl);
//		if (signatureList == null) {
//			signatureList = new LinkedList<ExtendedSignature>();
//			bodyMap.put(typeDecl, signatureList);
//		}
//		signatureList.add(new ExtendedSignature(methAbs, featureID));
//	}
//
//	private void copyComment(IRoleElement element, int id, String fullName) {
//		if (fullName == null) {
//			return;
//		}
//		AbstractSignature sig = signatureTable.get(fullName);
//
//		if (sig != null) {
//			final FOPFeatureData[] ids = (FOPFeatureData[]) sig.getFeatureData();
//			for (int j = 0; j < ids.length; j++) {
//				FOPFeatureData featureData = ids[j];
//				if (featureData.getID() == id) {
//					featureData.setComment(element.getJavaDocComment());
//					break;
//				}
//			}
//		}
//	}
//
//	private void copyComment_rec(FSTClassFragment classFragment, int id, String fullName) {
//		copyComment(classFragment, id, fullName);
//		for (FSTField field : classFragment.getFields()) {
//			copyComment(field, id, fullName + "." + field.getName());
//		}
//		for (FSTMethod method : classFragment.getMethods()) {
//			copyComment(method, id, fullName + "." + method.getName());
//		}
//		for (FSTClassFragment innerClasses : classFragment.getInnerClasses()) {
//			copyComment_rec(innerClasses, id, fullName + "." + innerClasses.getName());
//		}
//	}
}
