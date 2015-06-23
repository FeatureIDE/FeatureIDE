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

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IMember;
import org.eclipse.jdt.core.IPackageDeclaration;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.CompilationUnit;

import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiClassSignature;

/**
 * TODO description
 * 
 * @author steffen
 */
public class RefactoringUtil {

	
	public static CompilationUnit parseUnit(ICompilationUnit unit) {
	    ASTParser parser = ASTParser.newParser(AST.JLS4);
	    parser.setKind(ASTParser.K_COMPILATION_UNIT);
	    parser.setSource(unit);
	    parser.setResolveBindings(true);
	    parser.setBindingsRecovery(true);
	    return (CompilationUnit) parser.createAST(null); 
	  }
	
	public static boolean hasSameClass(final AbstractSignature signature, final IMember member) {
		final IType declaringType = member.getDeclaringType();
		String className;
		if (declaringType != null)
			className = member.getDeclaringType().getElementName();
		else
			className = member.getElementName();
		
		return signature.getName().equals(className) && hasSamePackage(signature, member);
	}
	
	private static boolean hasSamePackage(AbstractSignature signature, final IMember member) {
		
		String sigPackage;
		if (signature instanceof FujiClassSignature)
			sigPackage = ((FujiClassSignature) signature).getPackage();
		else
			sigPackage = signature.getParent().getPackage();
			
		String package0 = getPackageDeclaration(member.getCompilationUnit());
		
		return sigPackage.equals(package0);
	}

	public static String getPackageDeclaration(final ICompilationUnit unit) {
		IPackageDeclaration[] packageDeclarations = null;
		try {
			packageDeclarations = unit.getPackageDeclarations();
		} catch (JavaModelException e) {
			//TODO: 
			e.printStackTrace();
		}
		
		String package0 = "";
		if ((packageDeclarations != null) && (packageDeclarations.length > 0))
			package0 = packageDeclarations[0].getElementName();
		return package0;
	}
	
	public static boolean hasSameName(final AbstractSignature signature, final IMember member) {
		return hasSameName(signature, member.getElementName());
	}
	
	public static boolean hasSameName(final AbstractSignature signature, final String name) {
		return signature.getName().equals(name);
	}

}
