package de.ovgu.featureide.core.typecheck;

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import AST.BodyDecl;
import AST.ClassDecl;
import AST.CompilationUnit;
import AST.ConstructorDecl;
import AST.FieldDeclaration;
import AST.MethodDecl;
import AST.Program;
import AST.TypeDecl;
import fuji.Composition;
import fuji.Main;

/**
 * 
 * @author Sönke Holthusen
 * 
 */
public class FujiWrapper {

	public static HashMap<String, HashMap<String, TypeDecl>> internal_classes;

	public FujiWrapper() {
		internal_classes = new HashMap<String, HashMap<String, TypeDecl>>();
	}

	public void getAST(String featurePath, List<String> features) {
		for (String feature : features) {
			getAST(featurePath, feature);
		}
	}

	public void getAST(String featurePath, String feature) {
		StringBuffer buff = new StringBuffer();
		buff.append("AST for feature \"");
		buff.append(feature);

		System.out.println(buff);

		String[] fuji_options = { "-progmode", "-basedir", featurePath };
		List<String> feature_list = new LinkedList<String>();
		feature_list.add(feature);

		List<CompilationUnit> local_classes = new LinkedList<CompilationUnit>();
		List<CompilationUnit> external_classes = new LinkedList<CompilationUnit>();

		try {
			Main m = new Main(fuji_options, feature_list);

			/* Bereite die composition vor. */
			Composition composition = m.getComposition(m);

			Iterator<Program> ast_iter = composition.getASTIterator();

			while (ast_iter.hasNext()) {
				Program ast = ast_iter.next();

				Iterator<CompilationUnit> it = ast.compilationUnitIterator();
				while (it.hasNext()) {
					CompilationUnit cu = it.next();
					if (cu.fromSource()) {
						local_classes.add(cu);
					} else {
						external_classes.add(cu);
					}
				}

			}

		} catch (Exception e) {

		}

		for (CompilationUnit cu : local_classes) {
			processLocalCU(cu);
		}
	}

	/**
	 * @param cu
	 */
	private void processExternalCU(CompilationUnit cu) {
		// StringBuilder sb = new StringBuilder();
		// sb.append("----------\n");
		// sb.append("ExternalCU: \n");
		// sb.append("\tName: " + cu.classQName() + "\n");
		// sb.append("  ");
		// System.out.println(sb);

	}

	/**
	 * @param it
	 * @param cu
	 */
	private void processLocalCU(CompilationUnit cu) {

		System.out.println("LocalCU Classname: " + cu.classQName());

		// Class-level
		for (TypeDecl type : cu.getTypeDeclList()) {
			System.out.println(type.dumpString());
			Collection<MethodDecl> methods = new LinkedList<MethodDecl>();
			Collection<FieldDeclaration> fields = new LinkedList<FieldDeclaration>();
			
			// Member-level (Fields, Methods, Constructor)
			for (BodyDecl body : type.getBodyDeclList()) {
				// System.out.println("\n" + body.dumpString());
				if (body instanceof MethodDecl) {
					methods.add((MethodDecl) body);
				} else if (body instanceof FieldDeclaration) {
					fields.add((FieldDeclaration) body);
				} else if (body instanceof ConstructorDecl)
				{
					
				}
			}

			for (FieldDeclaration field : fields) {
				System.out.println(field.dumpString());
			}

			for (MethodDecl method : methods) {
				System.out.println(method.dumpTree());
			}
		}
	}

	public static boolean hasSuperClass(ClassDecl cl, ClassDecl superclass) {
		if (cl.hasSuperclass()) {
			if (cl.superclass().equals(superclass)) {
				return true;
			} else {
				return hasSuperClass(cl.superclass(), superclass);
			}
		}
		return false;
	}
}
