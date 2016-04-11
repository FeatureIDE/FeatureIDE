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
package de.ovgu.featureide.fm.core.utils.modelmaker;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.nio.file.Paths;
import java.util.Collection;

import org.prop4j.Implies;
import org.prop4j.Literal;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.DefaultFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.Feature;
import de.ovgu.featureide.fm.core.base.querying.QueryEngine;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.io.FeatureModelWriterIFileWrapper;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelWriter;

public class ScanRunner {

    private static final String EXTERNAL_DEPENDENCY = "external dependencies";

	public static void main(String... args) {
       
        try (Scanner scanner = new Scanner(Paths.get("/Users/marcus/Workspaces/Java/FeatureIDE/"), "plugins", "de.ovgu.featureide.examples")) {
            scanner.skipFileTypes("class");
            scanner.skipFileNames(".");
            scanner.doit();

            Exporter.Content content = scanner.getExporter().getContent();
            printToOut(content.unresolved, filePrintStream("featureide_unresolved.csv"), "name");
            printToOut(content.parentof, filePrintStream("featureide_parentof.csv"), "parent;child");
            printToOut(content.feature, filePrintStream("featureide_feature.csv"), "name");
            printToOut(content.requires, filePrintStream("featureide_requires.csv"), "name");

            IFeatureModel model = DefaultFeatureModelFactory.getInstance().createFeatureModel();

            Feature root = DefaultFeatureModelFactory.getInstance().createFeature(model, "featureide");
            
            
            IFeature externalDependencyFeature = DefaultFeatureModelFactory.getInstance().createFeature(model, EXTERNAL_DEPENDENCY);
            model.addFeature(externalDependencyFeature);
            root.getStructure().addChild(externalDependencyFeature.getStructure());
            
            model = model.clone(root);
            
            for (String featuerName : content.feature) {
                IFeature feature = DefaultFeatureModelFactory.getInstance().createFeature(model, featuerName);
                model.addFeature(feature);
            }
            
            QueryEngine engine = model.query();
            
            for (String featuerName : content.unresolved) {
            	IFeature feature = DefaultFeatureModelFactory.getInstance().createFeature(model, featuerName);
            	
            	if (feature.getName().equals("package:core")) {
            		System.out.print("Add " + feature.getName());
            		
            	}
            	
                model.addFeature(feature);
                
                IFeature externalDependencies = engine.exactMatch(EXTERNAL_DEPENDENCY);
                externalDependencies.getStructure().addChild(feature.getStructure());    
                
            }
            
            engine.refreshIndex();
            
            for (Exporter.Pair<String> statement : content.parentof) {
            	
                IFeature parent = engine.exactMatch(statement.first);
                IFeature child = engine.exactMatch(statement.second);
                
                parent.getStructure().addChild(child.getStructure());
            }
            
            for (Exporter.Pair<String> statement : content.requires) {
            	
            	IFeature parent = engine.exactMatch(statement.first);
            	IFeature child = engine.exactMatch(statement.second);
            	
            	if (child.getName().equals("package:core")) {
	            	for (IFeature f : model.getFeatures()) {
	            		if (f.getName().equals("package:core")) {
	            			System.out.println("Has " + f.getName());
	            			System.out.println(f.getStructure().getParent().getFeature().getName());
	            			System.out.println(f.getStructure().getParent().getParent().getFeature().getName());
	            		}
	            	}
            	}
            	               
            	model.addConstraint(DefaultFeatureModelFactory.getInstance().createConstraint(model, new Implies(new Literal(statement.first), new Literal(statement.second))));
                
            }
            
            
       //     System.out.println(model);

            

            FeatureModelWriterIFileWrapper writer = new FeatureModelWriterIFileWrapper(new XmlFeatureModelWriter(model));
            writer.writeToFile(new File("/Users/marcus/temp/test.xml"));
            
            System.out.println("Ende");


        } catch (Exception e) {
            e.printStackTrace();
        }

    }

    private static PrintStream filePrintStream(String file) throws FileNotFoundException {
        return new PrintStream(new BufferedOutputStream(new FileOutputStream(file)));
    }

    private static <T> void printToOut(Collection<T> collection, PrintStream printStream, String header) {
        printStream.println(header);
        for (T t  : collection)
            printStream.println(t);
        printStream.flush();
        printStream.close();
    }


}
