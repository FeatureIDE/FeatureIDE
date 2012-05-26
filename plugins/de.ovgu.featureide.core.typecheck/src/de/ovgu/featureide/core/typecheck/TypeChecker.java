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
import de.ovgu.featureide.core.typecheck.check.MethodCheck;
import de.ovgu.featureide.core.typecheck.check.SuperClassCheck;
import de.ovgu.featureide.core.typecheck.check.TypeCheck;
import de.ovgu.featureide.core.typecheck.helper.Timer;
import de.ovgu.featureide.core.typecheck.parser.CUParser;
import de.ovgu.featureide.core.typecheck.parser.CUTable;
import de.ovgu.featureide.core.typecheck.parser.ClassTable;
import de.ovgu.featureide.core.typecheck.parser.Parser;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * TODO description
 * 
 * @author S�nke Holthusen
 */
public class TypeChecker {
	private IFeatureProject _project;
	private CUParser _cuparser;

	private CheckPluginManager _checks;
	
	private int runs = 0;

	public TypeChecker(IFeatureProject project) {
		_project = project;

		_checks = new CheckPluginManager(new SuperClassCheck()
		// , new TypeCheck()
		// , new MethodCheck()
		);

		_cuparser = new CUParser(_checks);
	}

	public void run() {
		TypecheckCorePlugin.logln("Starting parsing project "
				+ _project.getProjectName());
		_cuparser.timer.reset();

		FeatureModel fm = _project.getFeatureModel();

		List<Feature> concrete_features = new ArrayList<Feature>(
				fm.getConcreteFeatures());

		_cuparser.parse(_project.getSourcePath(), concrete_features);

		TypecheckCorePlugin.logln("Parsing finished... ("
				+ _cuparser.timer.getTime() + " ms)");
		TypecheckCorePlugin.logln("Running checks...");
		Timer timer = new Timer();
		timer.start();
		_checks.invokeChecks(fm);
		timer.stop();
		TypecheckCorePlugin.logln("Checks finished... (" + timer.getTime()
				+ " ms)");
		TypecheckCorePlugin.logln("Run #" + ++runs);
	}
}
