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

import static de.ovgu.featureide.fm.core.localization.StringTable.FUJI_SIGNATURES_LOADED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.LOADING_SIGNATURES_FOR;
import static de.ovgu.featureide.fm.core.localization.StringTable.NO_FSTMODEL_PROVIDED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.RESTRICTION;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.core.JavaProject;

import AST.ASTNode;
import AST.Access;
import AST.BodyDecl;
import AST.ClassDecl;
import AST.CompilationUnit;
import AST.ConstructorAccess;
import AST.ConstructorDecl;
import AST.FieldDeclaration;
import AST.ImportDecl;
import AST.InterfaceDecl;
import AST.List;
import AST.MemberClassDecl;
import AST.MemberInterfaceDecl;
import AST.MethodAccess;
import AST.MethodDecl;
import AST.ParameterDeclaration;
import AST.Program;
import AST.TypeAccess;
import AST.TypeDecl;
import AST.VarAccess;
import AST.VariableDeclaration;
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
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.ExtendedSignature;
import de.ovgu.featureide.core.signature.base.FOPFeatureData;
import de.ovgu.featureide.core.signature.base.FeatureDataConstructor;
import de.ovgu.featureide.core.signature.base.SignaturePosition;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiClassSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiFieldSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiLocalVariableSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.job.AStoppableJob;
import fuji.Composition;
import fuji.Main;
import fuji.SPLStructure;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Loads the signatures from Fuji.
 *
 * @author Sebastian Krieter
 * @author Marcus Pinnecke
 */
@SuppressWarnings("deprecation")
public class ExtendedFujiSignaturesJob extends AStoppableJob implements LongRunningMethod<ProjectSignatures>{

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
//
//		public void setAbsoluteFilePath(int featureID, String absoluteFilePath) {
//			if (ids.containsKey(featureID)) {
//				ids.get(featureID).setAbsoluteFilePath(absoluteFilePath);
//			}
//		}
//
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

	private final IFeatureProject featureProject;
	private final ProjectSignatures projectSignatures;
	private final FeatureDataConstructor featureDataConstructor;
	private final boolean checkTypeAst;
	private final boolean fuildFSTModel;
//
//	private final HashMap<AbstractSignature, SignatureReference> signatureSet = new HashMap<AbstractSignature, SignatureReference>();
//	private final HashMap<String, AbstractSignature> signatureTable = new HashMap<String, AbstractSignature>();
//
//	private final HashMap<ASTNode<?>, java.util.List<ExtendedSignature>> bodyMap = new HashMap<ASTNode<?>, java.util.List<ExtendedSignature>>();
//	private final ArrayList<ExtendedSignature> originalList = new ArrayList<ExtendedSignature>();
//	private final Hashtable<ExtendedSignature, ClassDecl> nonPrimitveTypesTable = new Hashtable<ExtendedSignature, ClassDecl>();
//
//	private final Map<String, AbstractClassSignature> classes = new HashMap<>();

	public ProjectSignatures getProjectSignatures() {
		return projectSignatures;
	}

	public ExtendedFujiSignaturesJob(IFeatureProject featureProject, boolean checkTypeAst, boolean fuildFSTModel) {
		super(LOADING_SIGNATURES_FOR + featureProject.getProjectName());
		this.featureProject = featureProject;
		this.projectSignatures = new ProjectSignatures(this.featureProject.getFeatureModel());
		this.featureDataConstructor = new FeatureDataConstructor(projectSignatures, FeatureDataConstructor.TYPE_FOP);
		this.checkTypeAst = checkTypeAst;
		this.fuildFSTModel = fuildFSTModel;
	}

	public ExtendedFujiSignaturesJob(IFeatureProject featureProject) {
		this(featureProject, true, true);
	}

//	private AbstractSignature addFeatureID(AbstractSignature sig, int featureID, int start, int end, int identifierStart, int identifierEnd,
//			String absoluteFilePath) {
//		SignatureReference sigRef = signatureSet.get(sig);
//		if (sigRef == null) {
//			sigRef = new SignatureReference(sig);
//			signatureSet.put(sig, sigRef);
//			signatureTable.put(sig.getFullName(), sig);
//		}
//
//		SignaturePosition position = getSignaturePosition(start, end, identifierStart, identifierEnd);
//		sigRef.addID((FOPFeatureData) featureDataConstructor.create(featureID, position));
//		sigRef.setAbsoluteFilePath(featureID, absoluteFilePath);
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

	private java.util.List<String> featureModulePathnames = null;

	@SuppressWarnings("rawtypes")
	private String getFeatureName(ASTNode astNode) {
		int featureID = astNode.featureID();

		String featurename = featureModulePathnames.get(featureID);
		return featurename.substring(featurename.lastIndexOf(File.separator) + 1);
	}

	@Override
	public ProjectSignatures execute(IMonitor monitor) throws Exception {
		throw new UnsupportedOperationException("Fuji is currently not supported.");
	}

//	protected boolean work() {
//		FeatureModel fm = featureProject.getFeatureModel();
//		fm.getAnalyser().setDependencies();
//
//		String sourcePath = featureProject.getSourcePath();
//		String[] fujiOptions = new String[] { "-" + Main.OptionName.CLASSPATH, getClassPaths(featureProject), "-" + Main.OptionName.PROG_MODE,
//				"-" + Main.OptionName.COMPOSTION_STRATEGY, Main.OptionName.COMPOSTION_STRATEGY_ARG_FAMILY // "-typechecker",
//				, "-" + Main.OptionName.BASEDIR, sourcePath };
//		SPLStructure spl = null;
//		Program ast;
//
//		try {
//			Main fuji = new Main(fujiOptions, fm, fm.getConcreteFeatureNames());
//			Composition composition = fuji.getComposition(fuji);
//			ast = composition.composeAST();
//
////			if (checkTypeAst)
//				fuji.typecheckAST(ast);
//
//			spl = fuji.getSPLStructure();
//			featureModulePathnames = spl.getFeatureModulePathnames();
//		} catch (RuntimeException e) {
//			throw e;
//		} catch (Exception e) {
//			FeatureHouseCorePlugin.getDefault().logError(e);
//			return false;
//		}
//
//		createSignatures(featureProject, ast);
//
//		FeatureHouseCorePlugin.getDefault().logInfo(FUJI_SIGNATURES_LOADED_);
//		return true;
//	}

	@SuppressWarnings("unchecked")
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
//			String absoluteFilePath = unit.relativeName();
//
//			for (TypeDecl rootTypeDecl : typeDeclList) {
//				stack.push(rootTypeDecl);
//				do {
//					TypeDecl typeDecl = stack.pop();
//
//					String name = typeDecl.name();
//					String modifierString = typeDecl.getModifiers().toString();
//					String typeString = null;
//
//					if (typeDecl instanceof ClassDecl) {
//						typeString = AbstractClassSignature.TYPE_CLASS;
//					} else if (typeDecl instanceof InterfaceDecl) {
//						typeString = AbstractClassSignature.TYPE_INTERFACE;
//					}
//
//					AbstractClassSignature parent = null;
//					if (!roleStack.isEmpty()) {
//						parent = roleStack.pop();
//					}
//					featurename = getFeatureName(typeDecl);
//					int featureID = projectSignatures.getFeatureID(featurename);
//
//					FujiClassSignature curClassSig = (FujiClassSignature) addFeatureID(new FujiClassSignature(parent, name, modifierString, typeString, pckg,
//							typeDecl, importList), featureID, typeDecl.getStart(), typeDecl.getEnd(), typeDecl.IDstart, typeDecl.IDend, absoluteFilePath);
//					findClassAccess(typeDecl, curClassSig, featureID, absoluteFilePath);
//
//					for (ImportDecl importDecl : importList) {
//						curClassSig.addImport(importDecl.toString());
//						findClassAccess(importDecl, curClassSig, featureID, absoluteFilePath);
//					}
//
//					if (typeDecl instanceof ClassDecl) {
//						ClassDecl classDecl = (ClassDecl) typeDecl;
//						ClassDecl superClass = classDecl.superclass();
//						if (!superClass.fullName().equals("java.lang.Object"))
//							findClassAccess(classDecl.getSuperClassAccess(), curClassSig, featureID, absoluteFilePath);
//						for (Access access : classDecl.getImplementsList()) {
//							findClassAccess(access, curClassSig, featureID, absoluteFilePath);
//						}
//					}
//					else if (typeDecl instanceof InterfaceDecl) {
//						for (Access access : ((InterfaceDecl) typeDecl).getSuperInterfaceIdList()) {
//							findClassAccess(access, curClassSig, featureID, absoluteFilePath);
//						}
//					}
//
//					classes.put(typeDecl.fullName(), curClassSig);
//
//					if (parent != null) {
//						parent.addMemberClass(curClassSig);
//					}
//
//					for (BodyDecl bodyDecl : typeDecl.getBodyDeclList()) {
//						typeDecl.getModifiers();
//						if (bodyDecl instanceof MethodDecl) {
//							MethodDecl method = (MethodDecl) bodyDecl;
//
//							modifierString = method.getModifiers().toString();
//							name = method.name();
//							TypeDecl type = method.type();
//
//							List<ParameterDeclaration> parameterList = method.getParameterList();
//							List<Access> exceptionList = method.getExceptionList();
//
//							featurename = getFeatureName(bodyDecl);
//							featureID = projectSignatures.getFeatureID(featurename);
//
//							AbstractSignature methAbs = addFeatureID(new FujiMethodSignature(curClassSig, name, modifierString, type, false, parameterList,
//									exceptionList), featureID, method.getStart(), method.getEnd(), method.IDstart, method.IDend, absoluteFilePath);
//							findMethodAccesses(method, methAbs, featureID, absoluteFilePath);
//							curClassSig.addMethod((FujiMethodSignature) methAbs);
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
//							AbstractSignature afield = addFeatureID(new FujiFieldSignature(curClassSig, name, modifierString, type, field), featureID,
//									field.getStart(), field.getEnd(), field.IDstart, field.IDend, absoluteFilePath);
//
//							findMethodAccesses(field, afield, featureID, absoluteFilePath);
//							curClassSig.addField((FujiFieldSignature) afield);
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
//								AbstractSignature constrAbs = addFeatureID(new FujiMethodSignature(curClassSig, name, modifierString, type, true,
//										parameterList, exceptionList), featureID, constructor.getStart(), constructor.getEnd(),
//										constructor.IDstart, constructor.IDend, absoluteFilePath);
//								findMethodAccesses(constructor, constrAbs, featureID, absoluteFilePath);
//								curClassSig.addMethod((FujiMethodSignature) constrAbs);
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
//						typeString = AbstractClassSignature.TYPE_CLASS;
//					} else if (typeDecl instanceof InterfaceDecl) {
//						typeString = AbstractClassSignature.TYPE_INTERFACE;
//					}
//
//					AbstractClassSignature parent = null;
//					if (!roleStack.isEmpty()) {
//						parent = roleStack.pop();
//					}
//					FujiClassSignature curClassSig = (FujiClassSignature) signatureSet.get(new FujiClassSignature(parent, name, modifierString, typeString,
//							pckg, typeDecl, importList)).sig;
//
//					java.util.List<ExtendedSignature> accessingSignatures = bodyMap.remove(typeDecl);
//					if (accessingSignatures != null) {
//						for (ExtendedSignature absSig : accessingSignatures) {
//							curClassSig.addInvocationSignature(absSig);
//						}
//					}
//
//					for (BodyDecl bodyDecl : typeDecl.getBodyDeclList()) {
//						typeDecl.getModifiers();
//						accessingSignatures = bodyMap.remove(bodyDecl);
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
//								sigRef = signatureSet
//										.get(new FujiMethodSignature(curClassSig, name, modifierString, type, false, parameterList, exceptionList));
//							} else if (bodyDecl instanceof FieldDeclaration) {
//								FieldDeclaration field = (FieldDeclaration) bodyDecl;
//
//								modifierString = field.getModifiers().toString();
//								name = field.name();
//								TypeDecl type = field.type();
//
//								sigRef = signatureSet.get(new FujiFieldSignature(curClassSig, name, modifierString, type, field));
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
//									sigRef = signatureSet.get(new FujiMethodSignature(curClassSig, name, modifierString, type, true, parameterList,
//											exceptionList));
//								}
//
////								FOPFeatureData[] featureData = (FOPFeatureData[]) curClassSig.getFeatureData();
////								for (int j = 0; j < featureData.length; j++) {
////									for (ExtendedSignature absSig : accessingSignatures) {
////										SignaturePosition position = new SignaturePosition(
////												Symbol.getLine(constructor.getStart()), Symbol.getLine(constructor.getEnd()),
////												Symbol.getColumn(constructor.IDstart), Symbol.getColumn(constructor.IDend));
////										featureData[j].addInvokedSignature(absSig.sig, position);
////									}
////								}
//							}
//							if (sigRef != null) {
//								for (ExtendedSignature absSig : accessingSignatures) {
//									FOPFeatureData[] featureData = (FOPFeatureData[]) absSig.getSig().getFeatureData();
//									for (int j = 0; j < featureData.length; j++) {
//										if (featureData[j].getID() == absSig.getFeatureID()) {
//											featureData[j].addCalledSignature(sigRef.sig);
//											break;
//										}
//									}
//
//									sigRef.sig.addInvocationSignature(absSig);
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
//			final FOPFeatureData[] featureData = (FOPFeatureData[]) extSig.getSig().getFeatureData();
//			for (int j = 0; j < featureData.length; j++) {
//				if (featureData[j].getID() == extSig.getFeatureID()) {
//					featureData[j].setUsesOriginal(true);
//					break;
//				}
//			}
//
//		}
//
//		for (Entry<ExtendedSignature, ClassDecl> extSig : nonPrimitveTypesTable.entrySet()) {
//			final FOPFeatureData[] featureData = (FOPFeatureData[]) extSig.getKey().getSig().getFeatureData();
//			for (int j = 0; j < featureData.length; j++) {
//				if (featureData[j].getID() == extSig.getKey().getFeatureID()) {
//					featureData[j].addUsedNonPrimitveType(extSig.getValue().name());
//					break;
//				}
//			}
//		}
//
//		for (Entry<ASTNode<?>, java.util.List<ExtendedSignature>> entry : bodyMap.entrySet()) {
//			for (ExtendedSignature absSig : entry.getValue()) {
//				if (absSig.getSig() instanceof AbstractMethodSignature) {
//					AbstractMethodSignature methSig = (AbstractMethodSignature) absSig.getSig();
//					if (methSig.isConstructor()) {
//						continue;
//					}
//				}
//				final FOPFeatureData[] featureData = (FOPFeatureData[]) absSig.getSig().getFeatureData();
//				for (int j = 0; j < featureData.length; j++) {
//					if (featureData[j].getID() == absSig.getFeatureID()) {
//						featureData[j].setUsesExternMethods(true);
//						break;
//					}
//				}
//			}
//		}
//
//		for (AbstractSignature signature : sigArray) {
//			if (!(signature instanceof AbstractClassSignature))
//				continue;
//
//			AbstractClassSignature classSignature = (AbstractClassSignature) signature;
//
//			String fullName = signature.getFullName();
//			if (fullName.startsWith("."))
//				fullName = fullName.substring(1);
//			for (String extend : classSignature.getExtendList()) {
//				if (classes.containsKey(extend)) {
//					classes.get(extend).addSubClass(fullName);
//				}
//			}
//
//			for (String implement : classSignature.getImplementList()) {
//				if (classes.containsKey(implement)) {
//					AbstractClassSignature implementClass = classes.get(implement);
//					if (implementClass.getType().equals(AbstractClassSignature.TYPE_INTERFACE))
//						implementClass.addSubClass(fullName);
//				}
//			}
//		}
//
//		if (fuildFSTModel)
//		{
//			fp.getComposer().buildFSTModel();
//			FSTModel fst = fp.getFSTModel();
//
//			if (fst == null) {
//				FeatureHouseCorePlugin.getDefault().logInfo(NO_FSTMODEL_PROVIDED_);
//			} else {
//				for (FSTFeature fstFeature : fst.getFeatures()) {
//					final int id = projectSignatures.getFeatureID(fstFeature.getName());
//
//					for (FSTRole fstRole : fstFeature.getRoles()) {
//						FSTClassFragment classFragment = fstRole.getClassFragment();
//						String fullName = (classFragment.getPackage() == null ? "" : classFragment.getPackage()) + "." + classFragment.getName();
//						if (fullName.endsWith(".java")) {
//							fullName = fullName.substring(0, fullName.length() - ".java".length());
//						}
//						copyComment_rec(classFragment, id, fullName);
//					}
//				}
//			}
//		}
//		projectSignatures.setSignatureArray(sigArray);
//		featureProject.getFSTModel().setProjectSignatures(projectSignatures);
//	}

//	private void findClassAccess(ASTNode<?> stmt, AbstractSignature methAbs, int featureID, String absoluteFilePath)
//	{
//		if (stmt == null)
//			return;
//
//		if (stmt instanceof TypeAccess) {
//			TypeAccess typeAccess = (TypeAccess) stmt;
//			TypeDecl typeDecl = typeAccess.type();
//
//			if (typeDecl.featureID() == -1) return;
//
//			String featurename = getFeatureName(typeDecl);
//			int typeDeclFeatureID = projectSignatures.getFeatureID(featurename);
//			if (typeDeclFeatureID > 0)
//			{
//				int featureID2 = projectSignatures.getFeatureID(featurename);
//				if (typeDecl instanceof ClassDecl){
//					ClassDecl classDecl = (ClassDecl) typeDecl;
//					if (classDecl.fullName().equals("java.lang.Object")) return;
//					putAccess(typeDecl, methAbs, featureID2, typeAccess.getStart(), typeAccess.getEnd(), typeAccess.IDstart, typeAccess.IDend);
//				} else if (typeDecl instanceof InterfaceDecl){
//					InterfaceDecl classDecl = (InterfaceDecl) typeDecl;
//					if (classDecl.fullName().equals("java.lang.Object")) return;
//					putAccess(typeDecl, methAbs, featureID2, typeAccess.getStart(), typeAccess.getEnd(), typeAccess.IDstart, typeAccess.IDend);
//				}
//			}
//		} else {
//			for (int i = 0; i < stmt.getNumChildNoTransform(); i++) {
//				findClassAccess(stmt.getChildNoTransform(i), methAbs, featureID, absoluteFilePath);
//			}
//		}
//	}

	private void findFieldAccess(ASTNode<?> stmt, AbstractSignature methAbs, int featureID, String absoluteFilePath) {
		if (stmt == null)
			return;

	}

//	private void findMethodAccesses(ASTNode<?> stmt, AbstractSignature methAbs, int featureID, String absoluteFilePath) {
//		if (stmt == null) {
//			return;
//		}
//
//		if (stmt instanceof MethodAccess) {
//			MethodAccess methodAccess = (MethodAccess) stmt;
//			if ("original".equals(methodAccess.name())) {
//				SignaturePosition position = getSignaturePosition(methodAccess.getStart(), methodAccess.getEnd(), methodAccess.IDstart, methodAccess.IDend);
//				originalList.add(new ExtendedSignature(methAbs, featureID, position));
//			} else {
//				putAccess(((MethodAccess) stmt).decl(), methAbs, featureID, methodAccess.getStart(), methodAccess.getEnd(), methodAccess.IDstart, methodAccess.IDend);
//			}
//
//			for (int i = 0; i < stmt.getNumChildNoTransform(); i++) {
//				findMethodAccesses(stmt.getChildNoTransform(i), methAbs, featureID, absoluteFilePath);
//			}
//		} else if (stmt instanceof ConstructorAccess) {
//			ConstructorAccess conAccess = (ConstructorAccess) stmt;
//			putAccess(conAccess.decl(), methAbs, featureID, conAccess.getStart(), conAccess.getEnd(), conAccess.IDstart, conAccess.IDend);
//			for (int i = 0; i < stmt.getNumChildNoTransform(); i++) {
//				findMethodAccesses(stmt.getChildNoTransform(i), methAbs, featureID, absoluteFilePath);
//			}
//		} else if (stmt instanceof ConstructorDecl) {
//			ConstructorDecl conDecl = (ConstructorDecl) stmt;
//			putAccess(conDecl, methAbs, featureID, conDecl.getStart(), conDecl.getEnd(), conDecl.IDstart, conDecl.IDend);
//			for (int i = 0; i < stmt.getNumChildNoTransform(); i++) {
//				findMethodAccesses(stmt.getChildNoTransform(i), methAbs, featureID, absoluteFilePath);
//			}
//		} else if (stmt instanceof VarAccess) {
//			VarAccess variableAccess = (VarAccess) stmt;
//			Iterator<?> declIt = variableAccess.decls().iterator();
//			while (declIt.hasNext()) {
//				Object varAcess = declIt.next();
//				if (varAcess instanceof FieldDeclaration) {
//					FieldDeclaration fieldDecl = (FieldDeclaration) varAcess;
//					putAccess(fieldDecl, methAbs, featureID, variableAccess.getStart(), variableAccess.getEnd(), variableAccess.IDstart, variableAccess.IDend);
//				} else if (varAcess instanceof VariableDeclaration) {
//					VariableDeclaration varDecl = (VariableDeclaration) varAcess;
//					SignatureReference sigRef = signatureSet.get(new FujiLocalVariableSignature(methAbs.getParent(), (AbstractMethodSignature) methAbs, varDecl.name(), varDecl.getModifiers()
//							.toString(), varDecl.type()));
//					if (sigRef != null)
//					{
//						SignaturePosition position = getSignaturePosition(varDecl.getStart(), varDecl.getEnd(), varDecl.IDstart, varDecl.IDend);
//						sigRef.sig.addInvocationSignature(new ExtendedSignature(methAbs, featureID, position));
//					}
//				} else if (varAcess instanceof ParameterDeclaration) {
//					ParameterDeclaration varDecl = (ParameterDeclaration) varAcess;
//					SignatureReference sigRef = signatureSet.get(new FujiLocalVariableSignature(methAbs.getParent(), (AbstractMethodSignature) methAbs, varDecl.name(), varDecl.getModifiers()
//							.toString(), varDecl.type()));
//
//					if (sigRef != null)
//					{
//						SignaturePosition position = getSignaturePosition(varDecl.getStart(), varDecl.getEnd(), varDecl.IDstart, varDecl.IDend);
//						sigRef.sig.addInvocationSignature(new ExtendedSignature(methAbs, featureID, position));
//					}
//				}
//
//				for (int i = 0; i < stmt.getNumChildNoTransform(); i++) {
//					findMethodAccesses(stmt.getChildNoTransform(i), methAbs, featureID, absoluteFilePath);
//				}
//			}
//		} else if (stmt instanceof VariableDeclaration) {
//			VariableDeclaration varDecl = (VariableDeclaration) stmt;
//			if (varDecl.isLocalVariable())
//			{
//				addFeatureID(new FujiLocalVariableSignature(methAbs.getParent(), (AbstractMethodSignature) methAbs, varDecl.name(), varDecl.getModifiers()
//					.toString(), varDecl.type()), featureID, varDecl.getStart(), varDecl.getEnd(), varDecl.IDstart, varDecl.IDend, absoluteFilePath);
//			}
//			for (int i = 0; i < stmt.getNumChildNoTransform(); i++) {
//				findMethodAccesses(stmt.getChildNoTransform(i), methAbs, featureID, absoluteFilePath);
//			}
//		} else if (stmt instanceof ParameterDeclaration) {
//			ParameterDeclaration varDecl = (ParameterDeclaration) stmt;
//			addFeatureID(new FujiLocalVariableSignature(methAbs.getParent(), (AbstractMethodSignature) methAbs, varDecl.name(), varDecl.getModifiers()
//					.toString(), varDecl.type()), featureID, varDecl.getStart(), varDecl.getEnd(), varDecl.IDstart, varDecl.IDend, absoluteFilePath);
//			for (int i = 0; i < stmt.getNumChildNoTransform(); i++) {
//				findMethodAccesses(stmt.getChildNoTransform(i), methAbs, featureID, absoluteFilePath);
//			}
//		} else if (stmt instanceof TypeAccess) {
//			TypeAccess typeAccess = (TypeAccess) stmt;
//			TypeDecl typeDecl = typeAccess.type();
//			if (typeDecl.featureID() > 0)
//			{
//			String featurename = getFeatureName(typeDecl);
//			int featureID2 = projectSignatures.getFeatureID(featurename);
//			if (typeDecl instanceof ClassDecl){
//				ClassDecl classDecl = (ClassDecl) typeDecl;
//				if (classDecl.fullName().equals("java.lang.Object")) return;
//				putAccess(typeDecl, methAbs, featureID2, typeAccess.getStart(), typeAccess.getEnd(), typeAccess.IDstart, typeAccess.IDend);
//			} else if (typeDecl instanceof InterfaceDecl){
//				InterfaceDecl classDecl = (InterfaceDecl) typeDecl;
//				if (classDecl.fullName().equals("java.lang.Object")) return;
//					putAccess(typeDecl, methAbs, featureID2, typeAccess.getStart(), typeAccess.getEnd(), typeAccess.IDstart, typeAccess.IDend);
//				}
//			}
//
//			Iterator<?> iterator = typeAccess.decls().iterator();
//			while (iterator.hasNext()) {
//				Object cur = iterator.next();
//				if (cur instanceof ClassDecl) {
//					ClassDecl classDecl = (ClassDecl) cur;
//					if (classDecl.fullName().equals("java.lang.Object"))
//						continue;
//
//					SignaturePosition position = getSignaturePosition(typeAccess.getStart(), typeAccess.getEnd(), typeAccess.IDstart, typeAccess.IDend);
//					nonPrimitveTypesTable.put(new ExtendedSignature(methAbs, featureID, position), classDecl);
//					break;
//				}
//			}
//
//			for (int i = 0; i < stmt.getNumChildNoTransform(); i++) {
//				findMethodAccesses(stmt.getChildNoTransform(i), methAbs, featureID, absoluteFilePath);
//			}
//
//		} else {
//			for (int i = 0; i < stmt.getNumChildNoTransform(); i++) {
//				findMethodAccesses(stmt.getChildNoTransform(i), methAbs, featureID, absoluteFilePath);
//			}
//		}
//	}

	private SignaturePosition getSignaturePosition(final int start, final int end,  final int identifierStart, final int identifierEnd) {
		return new SignaturePosition(Symbol.getLine(start), Symbol.getLine(end), Symbol.getColumn(start), Symbol.getColumn(end),
				Symbol.getColumn(identifierStart), Symbol.getColumn(identifierEnd));
	}

//	private void putAccess(ASTNode<?> typeDecl, AbstractSignature methAbs, int featureID, int start, int end, int identifierStart, int identifierEnd) {
//		java.util.List<ExtendedSignature> signatureList = bodyMap.get(typeDecl);
//		if (signatureList == null) {
//			signatureList = new LinkedList<ExtendedSignature>();
//			bodyMap.put(typeDecl, signatureList);
//		}
//		SignaturePosition position = getSignaturePosition(start, end, identifierStart, identifierEnd);
//
//		signatureList.add(new ExtendedSignature(methAbs, featureID, position));
//	}

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

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.job.AbstractJob#work(de.ovgu.featureide.fm.core.job.monitor.IMonitor)
	 */
	@Override
	protected Object work(IMonitor workMonitor) throws Exception {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.job.AStoppableJob#work()
	 */
	@Override
	protected boolean work() throws Exception {
		// TODO Auto-generated method stub
		return false;
	}
}
