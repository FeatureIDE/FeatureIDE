/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.featurehouse.refactoring;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.base.AFeatureData;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.ExtendedSignature;
import de.ovgu.featureide.core.signature.base.FOPFeatureData;
import de.ovgu.featureide.core.signature.base.SignaturePosition;

/**
 * TODO description
 * 
 * @author Steffen Schulze
 */
public class FujiSelector {
	
	private final ProjectSignatures projectSignatures;
	private final String file;
	
	public FujiSelector(final IFeatureProject featureProject, final String file){
		this.file = file;
		this.projectSignatures = featureProject.getProjectSignatures();
	}
	
	public AbstractSignature getSelectedSignature(int line, int column){
		
		final SignatureIterator iter = projectSignatures.iterator();
		while (iter.hasNext()) {
			final AbstractSignature signature = iter.next();
			
			for (FOPFeatureData featureData : (FOPFeatureData[]) signature.getFeatureData()) {
				if (isSignatureSelected(featureData, featureData.getSigPosition(), line, column))
					return signature;
			}
			
			for (ExtendedSignature invokedSig : signature.getInvocationSignatures()) {
				for (AFeatureData invokedFeatureData : invokedSig.getSig().getFeatureData()) {
					if (isSignatureSelected(invokedFeatureData, invokedSig.getPosition(), line, column))
						return signature;
				} 
			} 
		}
		
		return null;
	}
	
	private boolean isSignatureSelected(AFeatureData featureData, SignaturePosition sigPosition, int line, int column){
		return (featureData.getAbsoluteFilePath().equals(file) &&
				((sigPosition.getStartRow() == line) &&
				 (sigPosition.getIdentifierStart() <= column) && (sigPosition.getIdentifierEnd() >= column)));
	}
	
//	public AbstractSignature getSelectedSignature(int line, int column) {
//
//		Program ast = getFujiAst();
//		if (ast == null) return null;
//		
//		CompilationUnit unit = getCompilationUnit(ast, file);
//		if (unit == null) return null;
//		
//		ASTNode<?> result = findSelectedNode(unit, line, column);
//		if (result == null) return null;
//		if (result.featureID() < 0) return null;
//		
//		
//		
//		AbstractSignature selectedSignature = null;
//		if (result instanceof MethodDecl){
//			selectedSignature = getFujiMethodSignature((MethodDecl) result, ast);
//		}
//		else if (result instanceof ConstructorDecl){
//			selectedSignature = getFujiMethodSignature((ConstructorDecl) result, ast);
//		}	
//		else if (result instanceof TypeDecl){
//			selectedSignature = getFujiClassSignature((TypeDecl)result, ast);
//		}
//		else if (result instanceof FieldDeclaration){
//			selectedSignature = getFujiFieldSignature((FieldDeclaration)result, ast);
//		}
//		else if (result instanceof VariableDeclaration){
//			final FujiMethodSignature enclosedMethod = getEnclosedMethod((VariableDeclaration)result, ast);
//			selectedSignature = getFujiLocalVariableSignature((VariableDeclaration)result, enclosedMethod, ast);
//			final FOPFeatureData firstFeatureData = (FOPFeatureData) selectedSignature.getFirstFeatureData();
//			firstFeatureData.addInvokedSignature(enclosedMethod);
//		}
//		else if (result instanceof ParameterDeclaration){
//			final FujiMethodSignature enclosedMethod = getEnclosedMethod((ParameterDeclaration)result, ast);
//			selectedSignature = getFujiLocalVariableSignature((ParameterDeclaration)result, enclosedMethod, ast);
//			final FOPFeatureData firstFeatureData = (FOPFeatureData) selectedSignature.getFirstFeatureData();
//			firstFeatureData.addInvokedSignature(enclosedMethod);
//		}
//		
//		return selectedSignature;
//	}
//	
//	private FujiLocalVariableSignature getFujiLocalVariableSignature(final VariableDeclaration varDecl, final FujiMethodSignature enclosedMethod, final Program ast) {
//		final FujiLocalVariableSignature sig = new FujiLocalVariableSignature(getDeclaringClass(varDecl, ast), enclosedMethod, varDecl.name(), varDecl.getModifiers().toString(), varDecl.type());
//		createAndSetFeatureData(varDecl, ast, sig);
//		return sig;
//	}
//	
//	private FujiLocalVariableSignature getFujiLocalVariableSignature(final ParameterDeclaration varDecl, final FujiMethodSignature enclosedMethod, final Program ast) {
//		final FujiLocalVariableSignature sig = new FujiLocalVariableSignature(getDeclaringClass(varDecl, ast), enclosedMethod, varDecl.name(), varDecl.getModifiers().toString(), varDecl.type());
//		createAndSetFeatureData(varDecl, ast, sig);
//		return sig;
//	}
//
//	protected void createAndSetFeatureData(final ASTNode<?> node, final Program ast, final AbstractSignature sig) {
//		sig.setFeatureData(new FOPFeatureData[] {getFeatureData(node, ast)});
//	}
//
//	private FujiFieldSignature getFujiFieldSignature(final FieldDeclaration fieldDecl, final Program ast) {
//		final FujiFieldSignature sig = new FujiFieldSignature(getDeclaringClass(fieldDecl, ast), fieldDecl.name(), fieldDecl.getModifiers().toString(), fieldDecl.type());
//		createAndSetFeatureData(fieldDecl, ast, sig);
//		return sig;
//	}
//	
//	private FujiMethodSignature getFujiMethodSignature(final MethodDecl methodDecl, final Program ast) {
//		final FujiMethodSignature sig = new FujiMethodSignature(getDeclaringClass(methodDecl, ast), methodDecl.name(), methodDecl.getModifiers().toString(), methodDecl.type(), false, methodDecl.getParameterList(),  methodDecl.getExceptionList());
//		createAndSetFeatureData(methodDecl, ast, sig);
//		return sig;
//	}
//	
//	private FujiMethodSignature getFujiMethodSignature(final ConstructorDecl methodDecl, final Program ast) {
//		final FujiMethodSignature sig = new FujiMethodSignature(getDeclaringClass(methodDecl, ast), methodDecl.name(), methodDecl.getModifiers().toString(), methodDecl.type(), true, methodDecl.getParameterList(),  methodDecl.getExceptionList());
//		createAndSetFeatureData(methodDecl, ast, sig);
//		return sig;
//	}
//
//	private FujiClassSignature getFujiClassSignature(final TypeDecl typeDecl, final Program ast) {
//		
//		final String pckg = getPackage(typeDecl);
//		String typeString = null;
//		if (typeDecl instanceof ClassDecl) {
//			typeString = AbstractClassSignature.TYPE_CLASS;
//		} else if (typeDecl instanceof InterfaceDecl) {
//			typeString = AbstractClassSignature.TYPE_INTERFACE;
//		}
//		
//		final FujiClassSignature sig = new FujiClassSignature(getDeclaringClass(typeDecl, ast), typeDecl.name(), typeDecl.getModifiers().toString(), typeString, pckg, typeDecl, null);
//		createAndSetFeatureData(typeDecl, ast, sig);
//		return sig;
//	}
//	
//	private FOPFeatureData getFeatureData(final ASTNode<?> node, final Program ast) {
//		final String featurename = getFeatureName(node, ast);
//		final FOPFeatureData featureData = (FOPFeatureData) featureDataConstructor.create(projectSignatures.getFeatureID(featurename), Symbol.getLine(node.getStart()), Symbol.getLine(node.getEnd()));
//		featureData.setAbsoluteFilePath(file);
//		return featureData;
//	}
//
//	private FujiClassSignature getDeclaringClass(final ASTNode<?> node, final Program ast){
//		
//		ASTNode<?> parent = node.getParent();
//		
//		while(parent != null){
//			if (parent instanceof TypeDecl){
//				FujiClassSignature classSignature = getFujiClassSignature((TypeDecl) parent, ast);
//				final FOPFeatureData featureData = (FOPFeatureData) getFeatureData(node, ast);
//				final FOPFeatureData[] featureDatas = {featureData};
//				classSignature.setFeatureData(featureDatas);
//				return classSignature;
//			}
//			parent = parent.getParent();
//		}
//		return null;
//	}
//	
//	
//	private FujiMethodSignature getEnclosedMethod(final ASTNode<?> varDecl, final Program ast){
//		
//		ASTNode<?> parent = varDecl.getParent();
//		
//		while(parent != null){
//			if (parent instanceof MethodDecl) 
//				return getFujiMethodSignature((MethodDecl) parent, ast);
//			else if (parent instanceof ConstructorDecl)
//				return getFujiMethodSignature((ConstructorDecl) parent, ast);
//			parent = parent.getParent();
//		}
//		return null;
//	}
//	
//	private String getPackage(final ASTNode<?> node){
//		ASTNode<?> parent = node.getParent();
//		while(parent != null){
//			if (parent instanceof CompilationUnit){
//				return ((CompilationUnit) parent).packageName();
//			}
//			parent = parent.getParent();
//		}
//		return null;
//	}
//	
//	private String getFeatureName(final ASTNode<?> astNode, final Program ast) {
//		int featureID = astNode.featureID();
//
//		String featurename = ast.getSPLStructure().getFeatureModulePathnames().get(featureID);
//		return featurename.substring(featurename.lastIndexOf(File.separator) + 1);
//	}
//	
//	@SuppressWarnings("unchecked")
//	private CompilationUnit getCompilationUnit(final Program ast, final String fileName){
//		Iterator<AST.CompilationUnit> unitIter = ast.compilationUnitIterator();
//		while (unitIter.hasNext()) {
//			AST.CompilationUnit unit = unitIter.next();
//			if (unit.featureID() < 0) {
//				continue;
//			}
//			
//			if (fileName.equals(unit.relativeName())) 
//				return unit;
//		}
//		return null;
//	}
//	
//	private ASTNode<?> findSelectedNode(final ASTNode<?> stmt, int line, int column) {
//		if (stmt == null) {
//			return null;
//		}
//		
//		SignaturePosition positions = new SignaturePosition();
//		if ((stmt instanceof Opt) && (stmt.getParent() != null)) {
//			final ASTNode<?> node = stmt.getParent();
//			positions.setRow(node.getStart(), node.getEnd());
//			positions.setColumn(node.getStart(), node.getEnd());
//		}
//		else{
//			positions.setRow(stmt.getStart(), stmt.getEnd());
//			
//			if (stmt instanceof TypeDecl) 
//				positions.setColumn(((TypeDecl) stmt).IDstart, ((TypeDecl) stmt).IDend);
//			else if (stmt instanceof MethodDecl)
//				positions.setColumn(((MethodDecl) stmt).IDstart, ((MethodDecl) stmt).IDend);
//			else if (stmt instanceof ConstructorDecl) 
//				positions.setColumn(((ConstructorDecl) stmt).IDstart, ((ConstructorDecl) stmt).IDend);
//			else if (stmt instanceof FieldDeclaration)
//				positions.setColumn(((FieldDeclaration) stmt).IDstart, ((FieldDeclaration) stmt).IDend);
//			else if (stmt instanceof VariableDeclaration)
//				positions.setColumn(((VariableDeclaration) stmt).IDstart, ((VariableDeclaration) stmt).IDend);
//			else
//				positions.setColumn(stmt.getStart(), stmt.getEnd());
//		}
//		
//		if ((positions.getStartRow() <= line) && (positions.getEndRow() >= line)) {
//			if ((positions.getStartRow() == line) && (((positions.getStartColumn() <= column) && (positions.getEndColumn() >= column)) || (column == 0))) {
//
//				if (stmt instanceof VarAccess) {
//					Variable varDecl = ((VarAccess) stmt).varDecl();
//					if (varDecl instanceof FieldDeclaration)
//						return (FieldDeclaration) varDecl;
//					else if (varDecl instanceof VariableDeclaration)
//						return (VariableDeclaration) varDecl;
//					else if (varDecl instanceof ParameterDeclaration)
//						return (ParameterDeclaration) varDecl;
//				} else if (stmt instanceof MethodAccess) {
//					return ((MethodAccess) stmt).decl();
//				} else if (stmt instanceof ArrayTypeAccess) {
//					// hier passiert nichts. Check children
//				} else if (stmt instanceof TypeAccess) {
//					return ((TypeAccess) stmt).type();
//				} else if ((stmt instanceof TypeDecl) || (stmt instanceof MethodDecl) || (stmt instanceof ConstructorDecl)
//						|| (stmt instanceof FieldDeclaration) || (stmt instanceof VariableDeclaration) || (stmt instanceof ParameterDeclaration)) {
//					return stmt;
//				}
//			}
//			for (int i = 0; i < stmt.getNumChildNoTransform(); i++) {
//				ASTNode<?> result = findSelectedNode(stmt.getChildNoTransform(i), line, column);
//				if (result != null)
//					return result;
//			}
//		}
		
//		if ((symbolStartLine <= line) && (symbolEndLine >= line)) {
//			if ((symbolStartLine == line)) {
//				
//				int symbolStartColumn = 0;
//				int symbolEndColumn = 0;
//				if (stmt instanceof TypeDecl) {
//					TypeDecl method = (TypeDecl) stmt;
//					symbolStartColumn = Symbol.getColumn(method.IDstart);
//					symbolEndColumn = Symbol.getColumn(method.IDend);
//				}
//				else if (stmt instanceof MethodDecl){
//					MethodDecl method = (MethodDecl) stmt;
//					symbolStartColumn = Symbol.getColumn(method.IDstart);
//					symbolEndColumn = Symbol.getColumn(method.IDend);
//				}else if (stmt instanceof ConstructorDecl) {
//					ConstructorDecl method = (ConstructorDecl) stmt;
//					symbolStartColumn = Symbol.getColumn(method.IDstart);
//					symbolEndColumn = Symbol.getColumn(method.IDend);
//				}
//				else if (stmt instanceof FieldDeclaration){
//					FieldDeclaration field = (FieldDeclaration) stmt;
//					symbolStartColumn = Symbol.getColumn(field.IDstart);
//					symbolEndColumn = Symbol.getColumn(field.IDend);
//				}
//				else if (stmt instanceof VariableDeclaration){
//					VariableDeclaration field = (VariableDeclaration) stmt;
//					symbolStartColumn = Symbol.getColumn(field.IDstart);
//					symbolEndColumn = Symbol.getColumn(field.IDend);
//				}
//				else if ((stmt instanceof Opt) && (stmt.getParent() != null)){
//					symbolStartColumn = Symbol.getColumn(stmt.getParent().getStart());
//					symbolEndColumn = Symbol.getColumn(stmt.getParent().getEnd());
//				}
//				else
//				{
//					symbolStartColumn = Symbol.getColumn(stmt.getStart());
//					symbolEndColumn = Symbol.getColumn(stmt.getEnd());
//				}
				
//				if ((symbolStartColumn <= column) && (symbolEndColumn >= column)){
//					if (stmt instanceof VarAccess) {
//						Variable varDecl = ((VarAccess) stmt).varDecl();
//						if (varDecl instanceof FieldDeclaration)
//							return (FieldDeclaration) varDecl;
//						else if (varDecl instanceof VariableDeclaration)
//							return (VariableDeclaration) varDecl;
//					}else if (stmt instanceof MethodAccess){
//						return ((MethodAccess) stmt).decl();
//					}else if (stmt instanceof TypeAccess){
//						return ((TypeAccess) stmt).type();
//					}else if ((stmt instanceof TypeDecl) || (stmt instanceof MethodDecl) || (stmt instanceof ConstructorDecl)|| (stmt instanceof FieldDeclaration)|| (stmt instanceof VariableDeclaration)){
//						return stmt;
//					}
//				}
//			}
//			for (int i = 0; i < stmt.getNumChildNoTransform(); i++) {
//				ASTNode<?> result = findSelectedNode(stmt.getChildNoTransform(i), line, column);
//				if (result != null) return result;
//			}
//		}
//		return null;
//	}
//	
}
