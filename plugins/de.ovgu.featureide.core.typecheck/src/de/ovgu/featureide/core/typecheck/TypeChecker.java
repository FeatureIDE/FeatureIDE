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
package de.ovgu.featureide.core.typecheck;

import java.util.ArrayList;
import java.util.List;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.typecheck.checks.Checks;
import de.ovgu.featureide.core.typecheck.parser.ClassTable;
import de.ovgu.featureide.core.typecheck.parser.Parser;
import de.ovgu.featureide.fm.core.Feature;

/**
 * TODO description
 * 
 * @author Sönke Holthusen
 */
public class TypeChecker
{

	private IFeatureProject _project;
	private Parser _parser;
	private ClassTable _class_table;

	public TypeChecker(IFeatureProject project)
	{
		_project = project;
		_parser = new Parser();
	}

	public void run()
	{
		System.out.println("Starting parsing project " + _project.getProjectName());
		List<Feature> concrete_features = new ArrayList<Feature>(_project.getFeatureModel().getConcreteFeatures());

		// TODO: consider the userdefined feature order
		// if (_project.getFeatureModel().isFeatureOrderUserDefined()) {
		// _parser.parse(sourcePath, _project.getFeatureModel()
		// .getFeatureOrderList());
		// } else {

		_parser.parse(_project.getSourcePath(), (concrete_features));

		_class_table = _parser.getClassTable();

		// }

//		System.out.println(_class_table.toString());

		// for (Feature feature : features)
		// {
		// System.out.println("Classes Introduced or Refined by Feature " +
		// feature.getName());
		// for (ClassTableEntry entry :
		// _class_table.getClassesByFeature(feature.getName()))
		// {
		// System.out.println("\t" + entry.getClassName());
		// }
		// }
		//
		// for (String class_name : _class_table.getClassNames())
		// {
		// System.out.println("Features introducing or refining class " +
		// class_name);
		// for (ClassTableEntry entry :
		// _class_table.getFeaturesByClass(class_name))
		// {
		// System.out.println("\t" + entry.getFeatureName());
		// }
		// }
		//
		// for (ClassTableEntry entry : _class_table.getClasses())
		// {
		//
		// }

		System.out.println("Parsing finished... (" + _parser.timer.getTime() + " ms)");
		System.out.println("Checking superclasses...");
		Checks checks = new Checks(_project, _class_table);
		checks.superClassCheck();
		System.out.println("Superclass check finished...");
	}
}
