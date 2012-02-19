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

import org.eclipse.core.resources.IFile;

import AST.ClassDecl;
import de.ovgu.featureide.fm.core.Feature;

/**
 * TODO description
 * 
 * @author Sönke Holthusen
 */
public class ClassTableEntry {
	private Feature _feature;
	private ClassDecl _class_ast;
	private IFile _class_file;
	
	private long _class_file_modification_stamp;
	
	public ClassTableEntry(Feature feature, ClassDecl class_ast, IFile class_file)
	{
		_feature = feature;
		_class_ast = class_ast;
		_class_file = class_file;
		
		_class_file_modification_stamp = _class_file.getModificationStamp();
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
	
	public IFile getClassFile()
	{
		return _class_file;
	}
	
	public String toString()
	{
		return getFeatureName() + "." + getClassName();
	}
	
	public boolean needsUpdate()
	{
		return _class_file_modification_stamp != _class_file.getModificationStamp();
	}
}
