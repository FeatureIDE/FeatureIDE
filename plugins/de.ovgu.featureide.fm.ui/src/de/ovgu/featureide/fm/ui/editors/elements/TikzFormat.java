/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.editors.elements;

import java.util.List;

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.io.APersistentFormat;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Converts the Feature Model Diagram in a tex-format using tikz.
 *
 * @author Simon Wenk
 * @author Yang Liu
 */
public class TikzFormat extends APersistentFormat<IGraphicalFeatureModel> {

	public static final String ID = PluginID.PLUGIN_ID + ".format.fm." + TikzFormat.class.getSimpleName();

	private StringBuilder postProcessing(StringBuilder str) {
		final int strLength = str.length();
		StringBuilder newString = new StringBuilder();
		newString = newString.append(str);
		for (int i = 0, j = 0; i < strLength; ++i) {
			if (str.charAt(i) == '_') {
				newString.insert(i + j, '\\');
				++j;
			}
		}
		return newString;

	}

	private void printTree(String node, IGraphicalFeatureModel object, StringBuilder str) {
		final int numberOfChildren = object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().getChildrenCount();
		if (numberOfChildren == 0) {
			str.append("[" + node + "]");
		} else {
			str.append("[" + node + " ");
			final List<IFeatureStructure> nodesChildren =
				object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().getChildren();
			final Iterable<IFeatureStructure> myChildren = nodesChildren;
			for (final IFeatureStructure child : myChildren) {
				printTree(child.getFeature().getName(), object, str);
			}
			str.append("]");
		}
	}

	@Override
	public String write(IGraphicalFeatureModel object) {
		final StringBuilder str = new StringBuilder();
		str.append("\\documentclass[border=5pt]{standalone}\n" + "%---required packages & variable definitions------------------------------------\n"
			+ "\\usepackage{forest}\n" + "\\usepackage{xcolor}\n" + "\\usetikzlibrary{angles}\n" + "\\definecolor{drawColor}{RGB}{128 128 128}\n"
			+ "\\newcommand{\\circleSize}{2.3pt}\n" + "\\newcommand{\\angleSize}{8.3pt}\n"
			+ "%-------------------------------------------------------------------------------\n"
			+ "%---Define the style of the tree------------------------------------------------\n" + "\\forestset{\n" + "	/tikz/mandatory/.style={\n"
			+ "		circle,fill=drawColor,\n" + "		draw=drawColor,\n" + "		inner sep=\\circleSize\n" + "	},\n" + "	/tikz/optional/.style={\n"
			+ "		circle,\n" + "		fill=white,\n" + "		draw=drawColor,\n" + "		inner sep=\\circleSize\n" + "	},\n"
			+ "	featureDiagram/.style={\n" + "		for tree={\n" + "			parent anchor = south,\n" + "			child anchor = north,\n"
			+ "			draw = drawColor,\n" + "			edge = {draw=drawColor},\n" + "			font = \\sffamily\n" + "		}\n" + "	},\n"
			+ "	abstract/.style={\n" + "		for tree={\n" + "		fill = blue!85!cyan!5\n" + "		}\n" + "	},\n" + "	concrete/.style={\n"
			+ "		for tree={\n" + "			fill = blue!85!cyan!20\n" + "		}\n" + "	},\n" + "	mandatory/.style={\n"
			+ "		edge label={node [mandatory] {} }\n" + "	},\n" + "	optional/.style={\n" + "		edge label={node [optional] {} }\n" + "	},\n"
			+ "	or/.style={\n" + "		tikz+={\n"
			+ "			\\path (.parent) coordinate (A) -- (!u.children) coordinate (B) -- (!ul.parent) coordinate (C) pic[fill=drawColor, angle radius=\\angleSize]{angle};\n"
			+ "		}	\n"
			+ "			%\\draw  (.children first) coordinate (A) -- () coordinate (B) -- (.children last) coordinate (C) pic[fill=drawColor, angle radius=5pt]{angle};}\n"
			+ "	},\n" + "	alternative/.style={\n" + "		tikz+={\n"
			+ "			\\path (.parent) coordinate (A) -- (!u.children) coordinate (B) -- (!ul.parent) coordinate (C) pic[draw=drawColor, angle radius=\\angleSize]{angle};\n"
			+ "		}	\n" + "	}\n" + "}\n" + "%-------------------------------------------------------------------------------\n" + "\\begin{document}\n"
			+ "	%---The Feature Diagram-----------------------------------------------------\n" + "	\\begin{forest}\n" + "		featureDiagram\n");
		// TODO: Tree implementation
		final Iterable<IFeature> myList = object.getFeatureModel().getFeatures();
		String myRoot = null;
		final int numberOfFeatures = object.getFeatureModel().getNumberOfFeatures();
		System.out.println("Number of Features: " + numberOfFeatures);

		for (final IFeature feature : myList) {
			System.out.println(feature + "\n");
			if (object.getGraphicalFeature(object.getFeatureModel().getFeature(feature.getName())).getObject().getStructure().isRoot()) {
				myRoot = feature.getName();
			}
		}

		// PRE-OREDER TRAVERSEL
		StringBuilder myTree = new StringBuilder();
		str.append("		");
		printTree(myRoot, object, myTree);
		myTree = postProcessing(myTree);
		str.append(myTree);
		str.append("\n");
		final String myChild =
			object.getGraphicalFeature(object.getFeatureModel().getFeature(myRoot)).getObject().getStructure().getFirstChild().getFeature().getName();
		System.out.println("erstes Kind der Wurzel: " + myChild);

		str.append("	\\end{forest}\n" + "	%---------------------------------------------------------------------------\n" + "\\end{document}");
		return str.toString();
	}

	@Override
	public boolean supportsRead() {
		return false;

	}

	@Override
	public boolean supportsWrite() {
		return true;

	}

	@Override
	public String getSuffix() {
		return ".tex";
	}

	@Override
	public String getName() {
		return "LaTeX-Document with TikZ";
	}

	@Override
	public String getId() {
		return ID;
	}

}
