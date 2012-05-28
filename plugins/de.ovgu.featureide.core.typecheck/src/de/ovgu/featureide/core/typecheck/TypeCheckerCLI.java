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
import de.ovgu.featureide.core.typecheck.check.SuperClassCheck;
import de.ovgu.featureide.core.typecheck.check.TypeCheck;
import de.ovgu.featureide.core.typecheck.parser.CUParser;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;

/**
 * TODO description
 * 
 * @author soenke
 */
public class TypeCheckerCLI {
    public static void main(String[] args) {
	String fmfile = args[0];
	String sourcepath = args[1];

	System.out.print("Reading FeatureModel from " + fmfile + "... ");
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
	List<Feature> concrete_features = new ArrayList<Feature>(
		fm.getConcreteFeatures());
	
	System.out.println("done");

	CheckPluginManager manager = new CheckPluginManager(new TypeCheck(), new SuperClassCheck());
	CUParser parser = new CUParser(manager);

	System.out.println("Parsing Feature in " + sourcepath);
	parser.parse(sourcepath, concrete_features);
	System.out.println("Parsing done...");

	System.out.println("Starting Checking...");
	manager.invokeChecks(fm);
	System.out.println("Checking done...");
    }
}
