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

import org.eclipse.osgi.internal.resolver.ComputeNodeOrder;

import AST.ASTNode;
import AST.CompilationUnit;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.typecheck.check.CheckPluginManager;
import de.ovgu.featureide.core.typecheck.check.SuperClassCheck;
import de.ovgu.featureide.core.typecheck.parser.CUParser;
import de.ovgu.featureide.core.typecheck.parser.CUTable;
import de.ovgu.featureide.core.typecheck.parser.ClassTable;
import de.ovgu.featureide.core.typecheck.parser.Parser;
import de.ovgu.featureide.fm.core.Feature;

/**
 * TODO description
 * 
 * @author S�nke Holthusen
 */
public class TypeChecker
{
	private IFeatureProject _project;
	private Parser _parser;
	private ClassTable _class_table;
	
	private CUTable cutable;
	private CUParser cuparser;

	private CheckPluginManager _checks;

	public TypeChecker(IFeatureProject project)
	{
		_project = project;
		_parser = new Parser(_project);
		_checks = new CheckPluginManager();
		
		cuparser = new CUParser(_checks);

		_checks.addCheck(new SuperClassCheck());
	}

	public void run()
	{
		TypecheckCorePlugin.logln("Starting parsing project " + _project.getProjectName());
		
		List<Feature> concrete_features = new ArrayList<Feature>(_project.getFeatureModel().getConcreteFeatures());

		// TODO: consider the userdefined feature order?

		//_parser.parseFeatures(_project.getSourcePath(), concrete_features);
		
		//_parser.parse(_project.getSourcePath(), (concrete_features));
		
		cuparser.parse(_project.getSourcePath(), concrete_features, true);

		_class_table = _parser.getClassTable();

		TypecheckCorePlugin.logln("Parsing finished... (" + cuparser.timer.getTime() + " ms)");
		TypecheckCorePlugin.logln("Running checks...");
		_checks.invokeChecks(_project, _class_table);
		TypecheckCorePlugin.logln("Checks finished...");
	}
}
