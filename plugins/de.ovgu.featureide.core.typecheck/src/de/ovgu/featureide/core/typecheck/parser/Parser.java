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
import java.util.Iterator;
import java.util.List;

import de.ovgu.featureide.fm.core.Feature;

import AST.CompilationUnit;
import AST.Program;
import AST.TypeDecl;

/**
 * TODO description
 * 
 * @author soenke
 */
public class Parser {
	private ClassTable _class_table;

	public Parser() {
		_class_table = new ClassTable();
	}

	public void parse(String feature_path, List<Feature> feature_list) {
		for (int i = 0; i < feature_list.size(); i++) {
			parseFeature(feature_path, feature_list.get(i));
		}
	}

	private void parseFeature(String feature_path, Feature feature) {

		try {
			List<String> list = new ArrayList<String>();
			list.add(feature.getName());
			
			Iterator<Program> iter = FujiWrapper.getFujiCompositionIterator(
					list, feature_path);
			
			while (iter.hasNext()) {
				Program ast = iter.next();

				@SuppressWarnings("unchecked")
				Iterator<CompilationUnit> it = ast.compilationUnitIterator();
				while (it.hasNext()) {
					CompilationUnit cu = it.next();
					if (cu.fromSource()) {
						parseCU(feature, cu);
					} else {
						
						// TODO: handle external classes
					}
				}

			}
			
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	private void parseCU(Feature feature, CompilationUnit cu)
	{
		for (TypeDecl type : cu.getTypeDeclList()) {
			parseClass(feature, type);
		}
	}
	
	private void parseClass(Feature feature, TypeDecl class_ast)
	{
		_class_table.add(feature, class_ast);
	}

	public ClassTable getClassTable()
	{
		return _class_table;
	}
}
