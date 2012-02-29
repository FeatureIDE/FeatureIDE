/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.core.typecheck.check;

import AST.Block;
import AST.Expr;
import AST.ExprStmt;
import AST.MethodDecl;
import AST.ReturnStmt;
import AST.Stmt;
import AST.VariableDeclaration;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.typecheck.parser.ClassTable;
import de.ovgu.featureide.core.typecheck.parser.ClassTableEntry;
import de.ovgu.featureide.fm.core.Feature;

/**
 * TODO description
 * 
 * @author S�nke Holthusen
 */
public class MethodCheck implements ICheckPlugin {

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.core.typecheck.check.ICheckPlugin#invokeCheck(de.ovgu
	 * .featureide.core.IFeatureProject,
	 * de.ovgu.featureide.core.typecheck.parser.ClassTable)
	 */
	@Override
	public void invokeCheck(IFeatureProject project, ClassTable class_table) {
		// possible method invocations
		// - Constructor
		// - Method body
		// - Field initialising (Var x = Class.staticMethod();)
		for (Feature feature : class_table.getFeatures()) {
			for (ClassTableEntry entry : class_table
					.getClassesByFeature(feature.getName())) {
				System.out.println(entry);
				System.out.println(entry.getAST().lookupMethod("addExtension(String)"));
				for (MethodDecl method : entry.getMethods()) {
					if (method.hasBlock()) {
						Block block = method.getBlock();
						//checkBlock(block);
					}
				}
			}
		}
	}

	private void checkBlock(Block block) {
		for (Stmt stmt : block.getStmtList()) {
			checkStatement(stmt);
		}
	}

	private void checkStatement(Stmt stmt) {
		if (stmt instanceof ExprStmt) {
			checkExpr(((ExprStmt) stmt).getExpr());
//			System.out.println("expr at line " + stmt.lineNumber());
		} else if (stmt instanceof ReturnStmt) {
			ReturnStmt returnstmt = (ReturnStmt) stmt;
			checkExpr(returnstmt.getResult());
		} else if (stmt instanceof VariableDeclaration)
		{
			VariableDeclaration varstmt = (VariableDeclaration) stmt;
			System.out.println(varstmt.getTypeAccess().packageName() + varstmt.getTypeAccess() + " " + varstmt.getID());
		}
		
		
		// TODO: get the enclosed statements
		// else if (stmt instanceof SwitchStmt) {
		// SwitchStmt switchstmt = (SwitchStmt) stmt;
		// } else if (stmt instanceof IfStmt) {
		// IfStmt ifstm = (IfStmt) stmt;
		// System.out.println("if at line " + stmt.lineNumber());
		// } else if (stmt instanceof WhileStmt) {
		// WhileStmt whilestm = (WhileStmt) stmt;
		// System.out.println("while at line " + stmt.lineNumber());
		// } else if (stmt instanceof DoStmt) {
		// DoStmt dostmt = (DoStmt) stmt;
		// System.out.println("do at line " + stmt.lineNumber());
		// } else if (stmt instanceof ForStmt) {
		// ForStmt forstmt = (ForStmt) stmt;
		// System.out.println("do at line " + stmt.lineNumber());
		// } else if (stmt instanceof BreakStmt) {
		//
		// } else if (stmt instanceof ContinueStmt) {
		//
		// } else if (stmt instanceof ThrowStmt) {
		//
		// } else if (stmt instanceof TryStmt) {
		//
		// } else if (stmt instanceof ContinueStmt) {
		//
		// }
	}

	private void checkExpr(Expr expr) {
//		System.out.println("EXPR: " + expr + " in line " + expr.lineNumber());
		

	}
}
