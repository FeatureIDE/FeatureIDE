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
import java.util.HashSet;

import org.eclipse.core.resources.IFile;

import AST.ClassDecl;
import AST.CompilationUnit;
import de.ovgu.featureide.fm.core.Feature;

/**
 * TODO description
 * 
 * @author Sönke Holthusen
 */
public class ClassTable
{

	// TODO: caching of classes

	private ArrayList<ClassTableEntry> _class_table = new ArrayList<ClassTableEntry>();
	private HashSet<String> _classes = new HashSet<String>();
	private HashSet<Feature> _features = new HashSet<Feature>();
	private HashMap<String, ArrayList<ClassTableEntry>> _classes_by_feature = new HashMap<String, ArrayList<ClassTableEntry>>();
	private HashMap<String, ArrayList<Feature>> _features_by_class = new HashMap<String, ArrayList<Feature>>();

	public ClassTable()
	{

	}

	public ClassDecl get(String feature, String classname)
	{
		for (ClassTableEntry entry : _classes_by_feature.get(feature))
		{
			if (entry.getClassName().equals(classname))
			{
				return entry.getAST();
			}
		}
		return null;
	}

	public boolean contains(String className)
	{
		return _classes.contains(className);
	}

	public ArrayList<ClassTableEntry> getClasses()
	{
		return _class_table;
	}

	public ArrayList<String> getClassNames()
	{
		return new ArrayList<String>(_classes);
	}

	public ArrayList<Feature> getFeatures()
	{
		return new ArrayList<Feature>(_features);
	}

	public ArrayList<ClassTableEntry> getClassesByFeature(String feature)
	{
		return _classes_by_feature.get(feature);
	}

	public ArrayList<Feature> getFeaturesByClass(String class_name)
	{
		return _features_by_class.get(class_name);
	}

	public boolean add(Feature feature, String feature_path, ClassDecl class_ast, CompilationUnit cu, IFile file)
	{
		ClassTableEntry entry = new ClassTableEntry(feature, feature_path, class_ast, cu, file);

		if (_class_table.contains(entry))
		{
			return false;
		}

		ArrayList<ClassTableEntry> class_entries = _classes_by_feature.get(feature.getName());
		ArrayList<Feature> feature_entries = _features_by_class.get(class_ast.fullName());

		if (class_entries == null)
		{
			class_entries = new ArrayList<ClassTableEntry>();
			_classes_by_feature.put(feature.getName(), class_entries);
		}

		if (feature_entries == null)
		{
			feature_entries = new ArrayList<Feature>();
			_features_by_class.put(class_ast.fullName(), feature_entries);
		}

		if (class_entries.contains(entry) || feature_entries.contains(entry))
		{
			return false;
		}

		_class_table.add(entry);
		_classes.add(entry.getClassName());
		_features.add(feature);
		class_entries.add(entry);
		feature_entries.add(feature);
		return true;
	}

	public ArrayList<Feature> featuresToUpdate()
	{
		ArrayList<Feature> update_needed = new ArrayList<Feature>();
		for (Feature feature : _features)
		{
			for (ClassTableEntry entry : getClassesByFeature(feature.getName()))
			{
				if (entry.needsUpdate())
				{
					update_needed.add(feature);
					break;
				}
			}
		}
		return update_needed;
	}

	@Override
	public String toString()
	{
		StringBuilder builder = new StringBuilder();
		for (ClassTableEntry entry : _class_table)
		{
			builder.append(entry).append("\n");
		}
		return builder.toString();
	}
}
