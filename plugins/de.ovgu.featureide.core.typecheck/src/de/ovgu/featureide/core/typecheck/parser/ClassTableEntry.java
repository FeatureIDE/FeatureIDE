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
package de.ovgu.featureide.core.typecheck.parser;

import java.util.ArrayList;

import de.ovgu.featureide.fm.core.Feature;
import AST.ClassDecl;
import AST.TypeDecl;

/**
 * TODO description
 * 
 * @author soenke
 */
public class ClassTableEntry {
	private Feature _feature;
	private ClassDecl _class_ast;
	private ArrayList<TypeDecl> _external_classes;
	
	public ClassTableEntry(Feature feature, ClassDecl class_ast)
	{
		_feature = feature;
		_class_ast = class_ast;
	}
	
	public String getFeatureName()
	{
		return _feature.getName();
	}
	
	public String getClassName()
	{
		return _class_ast.fullName();
	}
	
	public ClassDecl getAST()
	{
		return _class_ast;
	}
	
	public String toString()
	{
		return getFeatureName() + "." + getClassName();
	}
}
