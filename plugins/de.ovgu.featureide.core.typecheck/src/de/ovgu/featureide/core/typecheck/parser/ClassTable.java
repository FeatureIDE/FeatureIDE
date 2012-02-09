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
import java.util.HashMap;

import AST.TypeDecl;

/**
 * TODO description
 * 
 * @author soenke
 */
public class ClassTable {

	private ArrayList<ClassTableEntry> _class_table = new ArrayList<ClassTableEntry>();
	private HashMap<String, ArrayList<ClassTableEntry>> _feature_to_class_map = new HashMap<String, ArrayList<ClassTableEntry>>();

	public ClassTable() {

	}

	public TypeDecl get(String feature, String classname) {
		for (ClassTableEntry entry : _feature_to_class_map.get(feature)) {
			if (entry.getClassName().equals(classname)) {
				return entry.getAST();
			}
		}
		return null;
	}

	public boolean add(String feature, TypeDecl class_ast) {
		ClassTableEntry entry = new ClassTableEntry(feature, class_ast);

		if (_class_table.contains(entry)) {
			return false;
		}

		ArrayList<ClassTableEntry> entries = _feature_to_class_map.get(feature);

		if (entries == null) {
			entries = new ArrayList<ClassTableEntry>();
			_feature_to_class_map.put(feature, entries);
		}

		if (entries.contains(entry)) {
			return false;
		}

		_class_table.add(entry);
		entries.add(entry);
		return true;
	}

	public String dumpString() {
		StringBuilder builder = new StringBuilder();
		for (ClassTableEntry entry : _class_table) {
			builder.append(entry + "\n");
		}
		return builder.toString();
	}
}
