package de.ovgu.featureide.core.mpl.io;

import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
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
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.mpl.JavaInterfaceProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.io.constants.IOConstants;
import de.ovgu.featureide.core.mpl.io.parser.InterfaceParser;
import de.ovgu.featureide.core.mpl.signature.RoleMap;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassSignature;
import de.ovgu.featureide.core.mpl.signature.fuji.FujiClassSignature;
import de.ovgu.featureide.core.mpl.signature.fuji.FujiFieldSignature;
import de.ovgu.featureide.core.mpl.signature.fuji.FujiMethodSignature;
import de.ovgu.featureide.core.mpl.signature.fuji.FujiRole;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;
import fuji.Composition;
import fuji.Main;

@SuppressWarnings("restriction")
public final class FileLoader {

	public static Configuration loadConfiguration(
			JavaInterfaceProject interfaceProject) {
		try {
			ExtendedConfigurationReader exConfReader = new ExtendedConfigurationReader(
					interfaceProject);
			return exConfReader.read();
		} catch (Exception e) {
			MPLPlugin.getDefault().logError(e);
			return null;
		}
	}

	public static FeatureModel loadFeatureModel(
			JavaInterfaceProject interfaceProject) {
		try {
			FeatureModel featureModel = new FeatureModel();
			XmlFeatureModelReader reader = new XmlFeatureModelReader(
					featureModel);
			reader.readFromFile(interfaceProject.getProjectReference()
					.getFile(IOConstants.FILENAME_MODEL).getLocation().toFile());
			return featureModel;
		} catch (Exception e) {
			MPLPlugin.getDefault().logError(e);
			return null;
		}
	}

	public static RoleMap loadRoleMap(JavaInterfaceProject interfaceProject) {
		RoleMap roleMap = new RoleMap(interfaceProject);
		try {
			IFolder mainFolder = interfaceProject.getProjectReference()
					.getFolder(IOConstants.FOLDERNAME_FEATURE_ROLES);
			if (mainFolder.isAccessible()) {
				InterfaceParser parser = new InterfaceParser(
						interfaceProject.getViewTagPool(), roleMap);

				for (IResource featureFolder : mainFolder.members()) {
					if (featureFolder instanceof IFolder) {
						parser.setFeatureName(featureFolder.getName());
						for (IResource featureFolderMember : ((IFolder) featureFolder)
								.members()) {
							if (featureFolderMember instanceof IFolder) {
								IFolder packageFolder = (IFolder) featureFolderMember;
								for (IResource file : packageFolder.members()) {
									parser.setFile((IFile) file);
									roleMap.addRole(parser.read());
								}
							} else if (featureFolderMember instanceof IFile) {
								parser.setFile((IFile) featureFolderMember);
								roleMap.addRole(parser.read());
							}
						}
					}
				}
			}
			MPLPlugin.getDefault().logInfo("Local RoleMap loaded.");
			return roleMap;
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return null;
		}
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
	
	public static RoleMap fuijTest(JavaInterfaceProject interfaceProject, IFeatureProject featureProject) {
		FeatureModel fm = featureProject.getFeatureModel();
		fm.getAnalyser().setDependencies();

		String sourcePath = featureProject.getSourcePath();
		String[] fujiOptions = new String[] { "-" + Main.OptionName.CLASSPATH,
				getClassPaths(featureProject), "-" + Main.OptionName.PROG_MODE,
				"-" + Main.OptionName.COMPOSTION_STRATEGY,
				Main.OptionName.COMPOSTION_STRATEGY_ARG_FAMILY, //"-typechecker",
				"-basedir", sourcePath };
		Program ast = null;
//		fujiproject
//		lib
//		justyj
//		java.asd
		try {
			Main fuji = new Main(fujiOptions, fm, fm.getConcreteFeatureNames());
			Composition composition = fuji.getComposition(fuji);
			ast = composition.composeAST();
			fuji.typecheckAST(ast);
			featureModulePathnames = fuji.getSPLStructure().getFeatureModulePathnames();
		} catch (Exception e) {
			MPLPlugin.getDefault().logError(e);
			return null;
		}
		MPLPlugin.getDefault().logInfo("Fuji RoleMap loaded.");
		
		RoleMap roleMap = (interfaceProject == null) 
				? new RoleMap(fm)
				: new RoleMap(interfaceProject);
		LinkedList<TypeDecl> stack = new LinkedList<TypeDecl>();
		LinkedList<AbstractClassSignature> roleStack = new LinkedList<AbstractClassSignature>();
		
		@SuppressWarnings("unchecked")
		ASTNode<CompilationUnit> astNode = ast.getChildNoTransform(0);
		
		for (CompilationUnit unit : astNode) {
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
					FujiClassSignature curClassSig = (FujiClassSignature) roleMap.getSignatureRef(
							new FujiClassSignature(parent, name, modifierString, typeString, pckg, typeDecl, importList));					
					featurename = getFeatureName(typeDecl);
					curClassSig.addFeature(featurename);
					
					FujiRole curFujiRole = new FujiRole(featurename, curClassSig);
					roleMap.addRole(curFujiRole);
					
					for (BodyDecl bodyDecl : typeDecl.getBodyDeclList()) {
						typeDecl.getModifiers();
						if (bodyDecl instanceof MethodDecl) {
							MethodDecl method = (MethodDecl) bodyDecl;
							
							modifierString = method.getModifiers().toString();
							name = method.name();
							TypeDecl type = method.type();
							
							List<ParameterDeclaration> parameterList = method.getParameterList();
							List<Access> exceptionList = method.getExceptionList();
							
							FujiMethodSignature curMemberSig = (FujiMethodSignature) roleMap.getSignatureRef(new FujiMethodSignature(curClassSig, 
									name, modifierString, type, false, parameterList, exceptionList));
							featurename = getFeatureName(bodyDecl);
							curMemberSig.addFeature(featurename);
							
							curFujiRole.addMember(curMemberSig);
							
						} else if (bodyDecl instanceof FieldDeclaration) {
							FieldDeclaration field = (FieldDeclaration) bodyDecl;
							
							modifierString = field.getModifiers().toString();
							name = field.name();
							TypeDecl type = field.type();
							
							FujiFieldSignature curMemberSig = (FujiFieldSignature) roleMap.getSignatureRef(new FujiFieldSignature(curClassSig, 
									name, modifierString, type));
							featurename = getFeatureName(bodyDecl);
							curMemberSig.addFeature(featurename);
							
							curFujiRole.addMember(curMemberSig);
							
						} else if (bodyDecl instanceof ConstructorDecl) {
							ConstructorDecl constructor = (ConstructorDecl) bodyDecl;
							
							modifierString = constructor.getModifiers().toString();
							name = constructor.name();
							TypeDecl type = constructor.type();
							
							List<ParameterDeclaration> parameterList = constructor.getParameterList();
							List<Access> exceptionList = constructor.getExceptionList();
							
							FujiMethodSignature curMemberSig = (FujiMethodSignature) roleMap.getSignatureRef(new FujiMethodSignature(curClassSig, 
									name, modifierString, type, true, parameterList, exceptionList));
							featurename = getFeatureName(bodyDecl);
							curMemberSig.addFeature(featurename);
							
							curFujiRole.addMember(curMemberSig);
							
						} else if (bodyDecl instanceof MemberClassDecl) {
							stack.push(((MemberClassDecl)bodyDecl).getClassDecl());
							roleStack.push(curClassSig);
						} else if (bodyDecl instanceof MemberInterfaceDecl) {
							stack.push(((MemberInterfaceDecl)bodyDecl).getInterfaceDecl());
							roleStack.push(curClassSig);
						}
						
					}
				} while(!stack.isEmpty());
			}
			
//			LinkedList<TypeDecl> possibleSuperTypes = new LinkedList<TypeDecl>();
//			if (type instanceof ClassDecl) {
//				ClassDecl classDecl = (ClassDecl) type;
//				Opt<Access> superClasses = classDecl.getSuperClassAccessOpt();
//				for (Access access : superClasses) {
//					possibleSuperTypes.add(access.type());
//				}
//				for (Access access : classDecl.getImplementsList()) {
//					possibleSuperTypes.add(access.type());
//				}
//			} else if (type instanceof InterfaceDecl) {
//				InterfaceDecl interfaceDecl = (InterfaceDecl) type;
//				List<Access> superInterfaces = interfaceDecl.getSuperInterfaceIdList();
//				for (Access access : superInterfaces) {
//					possibleSuperTypes.add(access.type());
//				}
//			}
//			method.sameSignature(null);
		}
		return roleMap;
	}
	
	
	//	for (ReferenceType type : unit.getRefiningTypes()) {
	//	System.out.println();
	//	ReferenceType cur = type;
	//	BodyDecl ccc = cur.getBodyDecl(0);
	//	if (ccc instanceof MethodDecl) {
	//		MethodDecl dec = (MethodDecl) ccc;
	//		MemberDecl mdec = dec;
	//		MethodDecl dec4 = (MethodDecl) mdec.getParent().getChild(4);
	//		TypeAccess ret4 = (TypeAccess) dec4.getChild(1);
	//		TypeDecl decRet4 = ret4.decl();
	//
	//		MethodDecl dec7 = (MethodDecl) mdec.getParent().getChild(7);
	//		TypeAccess ret7 = (TypeAccess) dec7.getChild(1);
	//		TypeDecl decRet7 = ret7.decl();
	//
	//		boolean superT = decRet4
	//				.isSupertypeOfClassDecl((ClassDecl) decRet7);
	//
	//		System.out.println();
	//	}
	//	System.out.println();
	//}
	//// ReferenceType type =
	//
	//// unit.getRefiningTypes().
	//ASTNode n2 = unit.getParent();
	//CompilationUnit u = n2.compilationUnit();
	//
	//System.out.println();
	//Collection col = ast.getSPLStructure().getRoleGropus();
}
