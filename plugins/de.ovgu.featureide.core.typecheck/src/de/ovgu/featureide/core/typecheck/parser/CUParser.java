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

import fuji.SyntacticErrorException;
import guidsl.ParseException;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import AST.ASTNode;
import AST.CompilationUnit;
import AST.Program;
import Jakarta.DRAttributes.ParseErrorException;
import de.ovgu.featureide.core.typecheck.check.CheckPluginManager;
import de.ovgu.featureide.core.typecheck.helper.Directory;
import de.ovgu.featureide.core.typecheck.helper.Timer;
import de.ovgu.featureide.fm.core.Feature;

/**
 * TODO description
 * 
 * @author soenke
 */
public class CUParser {
	private Map<Feature, Directory> feature_directories = new HashMap<Feature, Directory>();

	public Timer timer;

	private CheckPluginManager plugins;

	/**
	 * 
	 */
	public CUParser(CheckPluginManager manager) {
		this.plugins = manager;
		this.timer = new Timer();
	}

	public void parse(String feature_path, List<Feature> feature_list) {
		for (int i = 0; i < feature_list.size(); i++) {
			parseFeature(feature_path, feature_list.get(i));
		}
	}

	private void parseFeature(String feature_path, Feature feature) {
		if (!feature_directories.containsKey(feature)) {
			feature_directories.put(feature, new Directory(new File(
					feature_path, feature.getName())));
		}

		if (!feature_directories.get(feature).changed()) {
			System.out.println("Feature " + feature.getName()
					+ " didn't change...");
		} else {
			Timer timer = new Timer();
			System.out.println("Parsing Feature " + feature.getName() + " ... ");
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
							// System.out.println(cu.pathName());
							parseAST(feature, cu);
						}
					}
				}
			} catch (SyntacticErrorException see) {
				System.out.println("Syntaxerror: " + see.getMessage());

			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			feature_directories.get(feature).update();
			this.timer.stop();
			timer.stop();
			System.out.println("Parsing finished (" + timer.getTime() + " ms)");
		}
	}

	public void parseAST(Feature feature, ASTNode node) {
		plugins.invokeNodeParse(feature, node);
		for (int i = 0; i < node.getNumChild(); i++) {
			parseAST(feature, node.getChild(i));
		}
	}
}
