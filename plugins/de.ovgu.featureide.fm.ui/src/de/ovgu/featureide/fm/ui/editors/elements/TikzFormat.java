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
import de.ovgu.featureide.fm.ui.GraphicsExporter;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Converts the Feature Model Diagram in a tex-format using tikz.
 *
 * @author Simon Wenk
 * @author Yang Liu
 */
public class TikzFormat extends APersistentFormat<IGraphicalFeatureModel> {

	public static class TikZHead extends APersistentFormat<IGraphicalFeatureModel> {

		@Override
		public String write(IGraphicalFeatureModel object) {
			final StringBuilder str = new StringBuilder();

			printHead(str);

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

	public static class TikZBody extends APersistentFormat<IGraphicalFeatureModel> {

		@Override
		public String write(IGraphicalFeatureModel object) {
			final StringBuilder str = new StringBuilder();

			printBody(str);

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

	public static class TikZMain extends APersistentFormat<IGraphicalFeatureModel> {

		@Override
		public String write(IGraphicalFeatureModel object) {
			StringBuilder str = new StringBuilder();

			str.append("\\begin{forest}\n	featureDiagram\n	");
			printTree(getRoot(object), object, str);
			str = postProcessing(str);
			str.append("\n\\end{forest}");

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

	public static final String ID = PluginID.PLUGIN_ID + ".format.fm." + TikzFormat.class.getSimpleName();

	private static StringBuilder postProcessing(StringBuilder str) {
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

	private static void insertNodeHead(String node, IGraphicalFeatureModel object, StringBuilder str) {
		str.append("[" + node);
		if (object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().isAbstract() == true) {
			str.append(",abstract");
		}
		if (object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().isConcrete() == true) {
			str.append(",concrete");
		}
		if ((object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().isRoot() == false)
			&& (object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().getParent().isAnd() == true)) {
			if (object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().isMandatory() == true) {
				str.append(",mandatory");
			} else {
				str.append(",optional");
			}
		}
		if (object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().isRoot() == false) {
			if ((object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().getParent().isOr() == true)
				&& (object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().getParent().getFirstChild()
						.equals(object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure()) == true)) {
				str.append(",or");
			}
		}
		if (object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().isRoot() == false) {
			if ((object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().getParent().isAlternative() == true)
				&& (object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().getParent().getFirstChild()
						.equals(object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure()) == true)) {
				str.append(",alternative");
			}
		}

	}

	private static void insertNodeTail(StringBuilder str) {
		str.append("]");
	}

	private static void printTree(String node, IGraphicalFeatureModel object, StringBuilder str) {
		final int numberOfChildren = object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().getChildrenCount();
		if (numberOfChildren == 0) {
			insertNodeHead(node, object, str);
			insertNodeTail(str);
		} else {
			insertNodeHead(node, object, str);
			final List<IFeatureStructure> nodesChildren =
				object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().getChildren();
			final Iterable<IFeatureStructure> myChildren = nodesChildren;
			for (final IFeatureStructure child : myChildren) {
				printTree(child.getFeature().getName(), object, str);
			}
			insertNodeTail(str);
		}
	}

	private static void printHead(StringBuilder str) {
		str.append("\\documentclass[border=5pt]{standalone}\n" + "%---required packages & variable definitions------------------------------------\n"
			+ "\\usepackage{forest}\n" + "\\usepackage{xcolor}\n" + "\\usetikzlibrary{angles}\n" + "\\definecolor{drawColor}{RGB}{128 128 128}\n"
			+ "\\newcommand{\\circleSize}{0.25em}\n" + "\\newcommand{\\angleSize}{0.8em}\n"
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
			+ "		}	\n" + "	},\n" + "	alternative/.style={\n" + "		tikz+={\n"
			+ "			\\path (.parent) coordinate (A) -- (!u.children) coordinate (B) -- (!ul.parent) coordinate (C) pic[draw=drawColor, angle radius=\\angleSize]{angle};\n"
			+ "		}	\n" + "	}\n" + "}\n" + "%-------------------------------------------------------------------------------\n");
	}

	private static void printBody(StringBuilder str) {
		str.append("\\input{head.tex}\n"); // Include head
		str.append("\\begin{document}\n	");
		str.append("\\input{" + GraphicsExporter.getFileName() + "}\n"); // Include main
		str.append("\\end{document}");
	}

	private static String getRoot(IGraphicalFeatureModel object) {
		final Iterable<IFeature> myList = object.getFeatureModel().getFeatures();
		String myRoot = null;

		for (final IFeature feature : myList) {
			if (object.getGraphicalFeature(object.getFeatureModel().getFeature(feature.getName())).getObject().getStructure().isRoot()) {
				myRoot = feature.getName();
				break;
			}
		}

		return myRoot;
	}

	@Override
	public String write(IGraphicalFeatureModel object) {
		final StringBuilder str = new StringBuilder();
		printHead(str);
		str.append("\\begin{document}\n" + "	%---The Feature Diagram-----------------------------------------------------\n" + "	\\begin{forest}\n"
			+ "		featureDiagram\n");

		// for debugging only
		final Iterable<IFeature> myList = object.getFeatureModel().getFeatures();
		final int numberOfFeatures = object.getFeatureModel().getNumberOfFeatures();
		System.out.println("Number of Features: " + numberOfFeatures);

		for (final IFeature feature : myList) {
			System.out.println(feature + "\n");
			// System.out.println(object.getGraphicalFeature(object.getFeatureModel().getFeature(feature.getStructure().getFirstChild().getFeature().getName()))
			// .getObject().getStructure().isOr());
		}
		System.out.println("FileName in TikZFormat class: " + GraphicsExporter.getFileName());
		// -------------------

		// PRE-OREDER TRAVERSEL
		StringBuilder myTree = new StringBuilder();
		str.append("		");
		printTree(getRoot(object), object, myTree);
		myTree = postProcessing(myTree);
		str.append(myTree);
		str.append("\n");

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
