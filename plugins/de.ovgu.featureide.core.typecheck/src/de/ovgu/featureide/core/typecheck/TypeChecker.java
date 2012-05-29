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

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.List;

import de.ovgu.featureide.core.typecheck.check.CheckPluginManager;
import de.ovgu.featureide.core.typecheck.check.TypeCheck;
import de.ovgu.featureide.core.typecheck.helper.Timer;
import de.ovgu.featureide.core.typecheck.parser.CUParser;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;

/**
 * TODO description
 * 
 * @author S�nke Holthusen
 */
public class TypeChecker {
    private CUParser _cuparser;

    private CheckPluginManager _checks;

    private String source_path;
    private FeatureModel fm;

    public static void main(String[] args) {
	if (args.length != 2) {
	    return;
	}
	String fmfile = args[0];
	String source_path = args[1];

	TypeChecker checker = new TypeChecker();
	
	checker.log("Reading feature model from file " + fmfile);
	FeatureModel fm = checker.readFM(fmfile);
	checker.log("\tdone");
	
	checker.setParameters(fm, source_path);
	checker.run();
    }

    public TypeChecker() {
	_checks = new CheckPluginManager(
	// new SuperClassCheck()
	// ,
		new TypeCheck()
	// ,
	// new MethodCheck()
	);

	_cuparser = new CUParser(_checks);
    }

    public void setParameters(FeatureModel fm, String source_path) {
	this.fm = fm;
	this.source_path = source_path;
    }

    public void run() {
	log("Starting parsing Features in " + source_path);
	_cuparser.timer.reset();

	List<Feature> concrete_features = new ArrayList<Feature>(
		fm.getConcreteFeatures());

	_cuparser.parse(source_path, concrete_features);

	log("Parsing finished... ("
		+ _cuparser.timer.getTime() + " ms)");
	log("Running checks...");
	Timer timer = new Timer();
	timer.start();
	_checks.invokeChecks(fm);
	timer.stop();
	log("Checks finished... (" + timer.getTime()
		+ " ms)");
    }

    public void log(String msg) {
	System.out.println(msg);
    }
    
    public FeatureModel readFM(String fmfile){
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
}
