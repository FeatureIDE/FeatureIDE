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
import java.util.Iterator;
import java.util.List;

import AST.ASTNode;
import AST.CompilationUnit;
import AST.IntrosRefsUtil;
import AST.MethodDecl;
import AST.Program;
import de.ovgu.featureide.core.typecheck.check.CheckPluginManager;
import de.ovgu.featureide.core.typecheck.helper.Timer;
import de.ovgu.featureide.fm.core.Feature;

/**
 * TODO description
 * 
 * @author soenke
 */
public class CUParser {
	private CUTable cutable;

	private Timer timer;

	private CheckPluginManager plugins;

	/**
	 * 
	 */
	public CUParser(CheckPluginManager manager) {
		this.plugins = manager;
		this.timer = new Timer();
	}

	public void parse(String feature_path, List<Feature> feature_list,
			boolean single_feature) {
		if (single_feature) {
			parse(feature_path, feature_list);
		} else {
			parseFeature(feature_path, feature_list);
		}
	}

	public void parse(String feature_path, List<Feature> feature_list) {
		for (int i = 0; i < feature_list.size(); i++) {
			parseFeature(feature_path, feature_list.subList(i, i + 1));
		}
	}

	private void parseFeature(String feature_path, List<Feature> features) {
		Timer timer = new Timer();
		if (features.size() == 1) {
			System.out.println("Parsing Feature " + features.get(0).getName()
					+ " ... ");
		} else {
			System.out.println("Parsing Features ...");
		}
		timer.start();
		this.timer.resume();

		try {
			List<String> list = new ArrayList<String>();
			for (Feature f : features) {
				list.add(f.getName());
			}

			Iterator<Program> iter = FujiWrapper.getFujiCompositionIterator(
					list, feature_path);

			while (iter.hasNext()) {
				// XXX: takes a very long time
				Program ast = iter.next();

				@SuppressWarnings("unchecked")
				Iterator<CompilationUnit> it = ast.compilationUnitIterator();
				while (it.hasNext()) {
					CompilationUnit cu = it.next();

					if (cu.fromSource()) {

						parseAST(cu);
						// List<MethodDecl> methods = FujiWrapper
						// .getMethodDecls(cu);
						// for (MethodDecl method : methods) {
						// System.out.println(method.hostPackage().toString()
						// + "." + method.hostType().name() + " "
						// + method.signature() + " Feature# "
						// + method.featureID());
						// }

						// System.out.println("At CompilationUnit " +
						// cu.pathName() + " " + cu.featureID());
						// cutable.addCU(features.get(cu.featureID()),
						// feature_path, cu);
					}
					// System.out.println();
				}

			}

		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		this.timer.stop();
		timer.stop();
		System.out.println("Parsing finished (" + timer.getTime() + " ms)");
	}

	public void parseAST(ASTNode node) {
		plugins.invokeNodeParse(node);
		for (int i = 0; i < node.getNumChild(); i++) {
			parseAST(node.getChild(i));
		}
	}
}
