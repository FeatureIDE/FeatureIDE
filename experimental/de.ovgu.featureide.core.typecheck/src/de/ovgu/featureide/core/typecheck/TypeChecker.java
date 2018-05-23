/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.core.typecheck;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.core.typecheck.check.CheckPluginManager;
import de.ovgu.featureide.core.typecheck.check.ICheckPlugin;
import de.ovgu.featureide.core.typecheck.check.MethodCheck;
import de.ovgu.featureide.core.typecheck.check.OriginalCheck;
import de.ovgu.featureide.core.typecheck.check.TypeReferenceCheck;
import de.ovgu.featureide.core.typecheck.correction.ConsoleProblemHandler;
import de.ovgu.featureide.core.typecheck.correction.IProblemHandler;
import de.ovgu.featureide.core.typecheck.correction.ProblemManager;
import de.ovgu.featureide.core.typecheck.helper.Timer;
import de.ovgu.featureide.core.typecheck.parser.Parser;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;

/**
 * TODO description
 * 
 * @author Soenke Holthusen
 */
public class TypeChecker {
    private Parser parser;

    private CheckPluginManager plugin_manager;
    private ProblemManager problem_manager;

    private String source_path;
    private FeatureModel fm;

    public static void main(String[] args) {
	if (args.length != 2) {
	    return;
	}
	String fmfile = args[0];
	String source_path = args[1];

	List<ICheckPlugin> plugins = new ArrayList<ICheckPlugin>();
	plugins.add(new MethodCheck());
	// plugins.add(new TypeCheck());
	// plugins.add(new FieldCheck());

	TypeChecker checker = new TypeChecker(defaultCheckPlugins(),
		defaultProblemHandlers());

	checker.log("Reading feature model from file " + fmfile);
	FeatureModel fm = checker.readFM(fmfile);
	checker.log("\tdone");

	checker.setParameters(fm, source_path);
	checker.run();
    }

    public TypeChecker(List<ICheckPlugin> plugins,
	    List<IProblemHandler> problem_handler) {
	plugin_manager = new CheckPluginManager(plugins);

	this.problem_manager = new ProblemManager(problem_handler);

	parser = new Parser(plugin_manager);
    }

    public void setParameters(FeatureModel fm, String source_path) {
	this.fm = fm;
	this.source_path = source_path;
    }

    public void run() {
	Timer all_timer = new Timer();
	all_timer.start();
	log("Starting parsing Features in " + source_path);
	parser.timer.reset();

	List<Feature> concrete_features = new ArrayList<Feature>(
		fm.getConcreteFeatures());

	parser.parse(source_path, concrete_features);

	log("Parsing finished... (" + parser.timer.getTime() + " ms)");

	if (parser.hasParseErrors()) {
	    System.out.println(parser.printParseErrors());
	} else {
	    log("Running checks...");
	    Timer timer = new Timer();
	    timer.start();
	    plugin_manager.invokeChecks(fm);
	    timer.stop();
	    log("Checks finished... (" + timer.getTime() + " ms)");
	    log("Problems reported:");
	    problem_manager.addProblems(plugin_manager.getProblems());
	    problem_manager.run();
	    log("Problem reporting finished");
	}
	log("Time needeed: " + all_timer.getTime() + "ms");
    }

    public void log(String msg) {
	problem_manager.log(msg);
    }

    public FeatureModel readFM(String fmfile) {
	FeatureModel fm = new FeatureModel();
	XmlFeatureModelReader reader = new XmlFeatureModelReader(fm);
	try {
	    reader.readFromFile(new File(fmfile));
	} catch (FileNotFoundException e) {
	    System.err.println("FeatureModel File " + fmfile
		    + " was not found!");
	    e.printStackTrace();
	} catch (UnsupportedModelException e) {
	    System.err.println("FeatureModel not supported!");
	    e.printStackTrace();
	}
	return fm;
    }

    // modified to work with a disjunction from FeatureModel.java
    private static Node disjunct(FeatureModel fm, Set<Feature> b) {
	Iterator<Feature> iterator = b.iterator();
	Node result = new Literal(NodeCreator.getVariable(iterator.next(), fm));
	while (iterator.hasNext())
	    result = new Or(result, new Literal(NodeCreator.getVariable(
		    iterator.next(), fm)));

	return result;
    }

    public static boolean checkImpliesDisjunct(FeatureModel fm, Set<Feature> a,
	    Set<Feature> b) throws TimeoutException {
	if (b.isEmpty())
	    return true;

	Node featureModel = NodeCreator.createNodes(fm);

	// B1 and B2 and ... Bn
	Node condition = disjunct(fm, b);
	// (A1 and ... An) => (B1 and ... Bn)
	if (!a.isEmpty())
	    condition = new Implies(disjunct(fm, a), condition);
	// FM => (A => B)
	Implies finalFormula = new Implies(featureModel, condition);
	return !new SatSolver(new Not(finalFormula), 1000).isSatisfiable();
    }
    
    public static List<ICheckPlugin> defaultCheckPlugins(){
	List<ICheckPlugin> plugins = new ArrayList<ICheckPlugin>();
	plugins.add(new TypeReferenceCheck());
	plugins.add(new OriginalCheck());
//	plugins.add(new FieldCheck());
//	plugins.add(new MethodCheck());
	return plugins;
    }
    
    public static List<IProblemHandler> defaultProblemHandlers(){
	List<IProblemHandler> problem_handler = new ArrayList<IProblemHandler>();
	problem_handler.add(new ConsoleProblemHandler());
//	problem_handler.add(new LogFileProblemHandler("log.txt"));
	return problem_handler;
    }
}
