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
package de.ovgu.featureide.core.typecheck.parser;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import AST.ASTNode;
import AST.CompilationUnit;
import AST.Problem;
import AST.Program;
import de.ovgu.featureide.core.typecheck.check.CheckPluginManager;
import de.ovgu.featureide.core.typecheck.helper.Directory;
import de.ovgu.featureide.core.typecheck.helper.FujiWrapper;
import de.ovgu.featureide.core.typecheck.helper.Timer;
import de.ovgu.featureide.fm.core.Feature;

/**
 * Parses feature modules using Fuji, gives the plug-ins access to the ASTs of
 * the features
 * 
 * @author Soenke Holthusen
 */
public class Parser {
    private Map<Feature, Directory> feature_directories = new HashMap<Feature, Directory>();

    public Timer timer;

    private CheckPluginManager plugins;

    private List<Problem> parse_errors = new ArrayList<Problem>();

    public Parser(CheckPluginManager manager) {
	this.plugins = manager;
	this.timer = new Timer();
    }

    /**
     * Takes a list of feature names and parses every feature on its own
     * 
     * @param feature_path
     *            the path to the feature modules
     * @param feature_list
     *            the list of features to parse
     */
    public void parse(String feature_path, List<Feature> feature_list) {
	for (int i = 0; i < feature_list.size(); i++) {
	    parseFeature(feature_path, feature_list.get(i));
	}
    }

    /**
     * Parses one feature
     * 
     * @param feature_path
     *            the path to the feature modules
     * @param feature
     *            the feature to parse
     */
    private void parseFeature(String feature_path, Feature feature) {
	boolean update_needed = true;

	if (!feature_directories.containsKey(feature)) {
	    feature_directories.put(feature, new Directory(new File(
		    feature_path, feature.getName())));
	} else if (!feature_directories.get(feature).changed()) {
	    System.out.println("Feature " + feature.getName()
		    + " ignored, no changes...");
	    update_needed = false;
	}

	if (update_needed) {
	    Timer timer = new Timer();
	    System.out
		    .println("Parsing Feature " + feature.getName() + " ... ");
	    timer.start();
	    this.timer.resume();

	    plugins.resetFeature(feature);

	    try {
		List<String> list = new ArrayList<String>();

		list.add(feature.getName());

		Iterator<Program> iter = FujiWrapper
			.getFujiCompositionIterator(list, feature_path);

		while (iter.hasNext()) {
		    // XXX: takes a very long time
		    Program ast = iter.next();

		    @SuppressWarnings("unchecked")
		    Iterator<CompilationUnit> it = ast
			    .compilationUnitIterator();
		    while (it.hasNext()) {
			CompilationUnit cu = it.next();

			if (cu.fromSource()) {
			    checkForSyntaxErrors(cu);
			    // System.out.println(cu.pathName());
			    parseAST(feature, cu);
			}
		    }
		}
	    } catch (Exception e) {
		e.printStackTrace();
	    }
	    feature_directories.get(feature).update();
	    this.timer.stop();
	    timer.stop();
	    System.out.println("Parsing finished (" + timer.getTime() + " ms)");
	}
    }

    /**
     * iterates the AST, lets the plug-in manager
     * 
     * @param feature
     * @param node
     */
    @SuppressWarnings("rawtypes")
    public void parseAST(Feature feature, ASTNode node) {
	plugins.invokeNodeParse(feature, node);
	for (int i = 0; i < node.getNumChild(); i++) {
	    parseAST(feature, node.getChild(i));
	}
    }

    /**
     * Checks if Fuji encountered syntax errors while parsing the feature module
     * 
     * @param cu
     *            the compilation unit
     */
    @SuppressWarnings("unchecked")
    public void checkForSyntaxErrors(CompilationUnit cu) {
	List<Problem> parseErrors = (List<Problem>) cu.parseErrors();
	if (!parseErrors.isEmpty()) {
	    parse_errors.addAll(parseErrors);
	}
    }

    /**
     * 
     * @return return true is the parser encountered syntax errors, false
     *         otherwise
     */
    public boolean hasParseErrors() {
	return !parse_errors.isEmpty();
    }

    public String printParseErrors() {
	StringBuilder message = new StringBuilder();
	for (Problem p : parse_errors) {
	    message.append(p + "\n");
	}
	return message.toString();
    }
}
