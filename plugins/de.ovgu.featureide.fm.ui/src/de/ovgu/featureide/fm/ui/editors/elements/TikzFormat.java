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
 * This class implements a LaTeX converter for the feature diagram (using TikZ). <br> The main class uses one String for the latex code; the subclasses divides
 * the code into three different Strings (each subclass for one String).
 *
 * @author Simon Wenk
 * @author Yang Liu
 */
public class TikzFormat extends APersistentFormat<IGraphicalFeatureModel> {

	static boolean[] legend = { false, false, false, false, false, false, false };

	private static final String lnSep = System.lineSeparator();

	/**
	 * Creates the styles and packages that are required for the converted Feature Model Diagram. <br> <br> <b>Note:</b> For exporting purposes the file name
	 * must be <i> head.tex </i> and exported in the same folder as the main file.
	 */
	public static class TikZHead extends APersistentFormat<IGraphicalFeatureModel> {

		/**
		 * Writes the required styles and packages in a String.
		 *
		 * @param object The graphic feature model
		 * @return LaTeX Code as a String
		 */
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

	/**
	 * Creates the body for the LaTeX export. <br> <br> <b>Note:</b> For exporting purposes the file name must be <i> body.tex </i> and exported in the same
	 * folder as the main file. This file runs only with the head file and the main file.
	 */
	public static class TikZBody extends APersistentFormat<IGraphicalFeatureModel> {

		private final String FileName;

		/**
		 * @param FileName The file name of the main file
		 */
		public TikZBody(String FileName) {
			this.FileName = FileName;
		}

		/**
		 * Constructs the body of the LaTeX file, includes the head file and the main file and writes it in a String.
		 *
		 * @param object The graphic feature model
		 * @return LaTeX Code as a String
		 */
		@Override
		public String write(IGraphicalFeatureModel object) {
			final StringBuilder str = new StringBuilder();

			printBody(str, FileName);

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

	/**
	 * Creates the main file. This contains the converted Feature Diagram. <br> </br>
	 *
	 * <b> Note: </b> The class <i> TikZHead </i> creates the styles and packages that are required to execute the resulting LaTeX Code correctly.
	 *
	 * @see {TikzHead}
	 */
	public static class TikZMain extends APersistentFormat<IGraphicalFeatureModel> {

		/**
		 * Writes the tree of the Feature Diagram in tex-format.
		 *
		 * @param object The graphic feature model
		 * @return LaTeX Code as a String
		 */
		@Override
		public String write(IGraphicalFeatureModel object) {
			StringBuilder str = new StringBuilder();

			str.append("\\begin{forest}" + lnSep + "	featureDiagram" + lnSep + "	");
			printTree(getRoot(object), object, str);
			str = postProcessing(str);
			str.append("	" + lnSep);
			printLegend(str, object.isLegendHidden());
			str.append("\\end{forest}");

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

	/**
	 * Processes a String to make special symbols LaTeX compatible.
	 *
	 * @param str a StringBuilder which content should be LaTeX code
	 * @return a StringBuilder which contend has compatible LaTeX code
	 */
	public static StringBuilder postProcessing(StringBuilder str) {
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
			legend[0] = true;
		}
		if (object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().isConcrete() == true) {
			str.append(",concrete");
			legend[1] = true;
		}
		if ((object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().isRoot() == false)
			&& (object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().getParent().isAnd() == true)) {
			if (object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().isMandatory() == true) {
				str.append(",mandatory");
				legend[2] = true;
			} else {
				str.append(",optional");
				legend[3] = true;
			}
		}
		if (object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().isRoot() == false) {
			if ((object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().getParent().isOr() == true)
				&& (object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().getParent().getFirstChild()
						.equals(object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure()) == true)) {
				str.append(",or");
				legend[4] = true;
			}
		}
		if (object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().isRoot() == false) {
			if ((object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().getParent().isAlternative() == true)
				&& (object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().getParent().getFirstChild()
						.equals(object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure()) == true)) {
				str.append(",alternative");
				legend[5] = true;
			}
		}
	}

	private static void insertNodeTail(StringBuilder str) {
		str.append("]");
	}

	private static void printTree(String node, IGraphicalFeatureModel object, StringBuilder str) {
		// PRE-OREDER TRAVERSEL
		final int numberOfChildren = object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().getChildrenCount();
		if ((numberOfChildren == 0)) {
			insertNodeHead(node, object, str);
			insertNodeTail(str);
		} else if (object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).isCollapsed()) {
			legend[6] = true;
			insertNodeHead(node, object, str);
			str.append("[,collapsed,edge label={node[hiddenNodes]{" + countNodes(node, object, -1) + "}}]");
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

	private static int countNodes(String node, IGraphicalFeatureModel object, int counter) {
		final int numberOfChildren = object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().getChildrenCount();
		if (numberOfChildren == 0) {
			return ++counter;
		} else {
			final List<IFeatureStructure> nodesChildren =
				object.getGraphicalFeature(object.getFeatureModel().getFeature(node)).getObject().getStructure().getChildren();
			final Iterable<IFeatureStructure> myChildren = nodesChildren;
			for (final IFeatureStructure child : myChildren) {
				counter = countNodes(child.getFeature().getName(), object, counter);

			}
			return ++counter;
		}
	}

	private static void printHead(StringBuilder str) {
		str.append("\\documentclass[border=5pt]{standalone}" + lnSep + "%---required packages & variable definitions------------------------------------"
			+ lnSep + "\\usepackage{forest}" + lnSep + "\\usepackage{xcolor}" + lnSep + "\\usetikzlibrary{angles}" + lnSep
			+ "\\definecolor{drawColor}{RGB}{128 128 128}" + lnSep + "\\newcommand{\\circleSize}{0.25em}" + lnSep + "\\newcommand{\\angleSize}{0.8em}" + lnSep
			+ "%-------------------------------------------------------------------------------" + lnSep
			+ "%---Define the style of the tree------------------------------------------------" + lnSep + "\\forestset{" + lnSep
			+ "	/tikz/mandatory/.style={" + lnSep + "		circle,fill=drawColor," + lnSep + "		draw=drawColor," + lnSep + "		inner sep=\\circleSize"
			+ lnSep + "	}," + lnSep + "	/tikz/optional/.style={" + lnSep + "		circle," + lnSep + "		fill=white," + lnSep + "		draw=drawColor,"
			+ lnSep + "		inner sep=\\circleSize" + lnSep + "	}," + lnSep + "	featureDiagram/.style={" + lnSep + "		for tree={" + lnSep
			+ "			parent anchor = south," + lnSep + "			child anchor = north," + lnSep + "			draw = drawColor," + lnSep
			+ "			edge = {draw=drawColor}," + lnSep + "		}" + lnSep + "	}," + lnSep + "	/tikz/abstract/.style={" + lnSep
			+ "		fill = blue!85!cyan!5," + lnSep + "		draw = drawColor" + lnSep + "	}," + lnSep + "	/tikz/concrete/.style={" + lnSep
			+ "		fill = blue!85!cyan!20," + lnSep + "		draw = drawColor" + lnSep + "	}," + lnSep + "	mandatory/.style={" + lnSep
			+ "		edge label={node [mandatory] {} }" + lnSep + "	}," + lnSep + "	optional/.style={" + lnSep + "		edge label={node [optional] {} }"
			+ lnSep + "	}," + lnSep + "	or/.style={" + lnSep + "		tikz+={" + lnSep
			+ "			\\path (.parent) coordinate (A) -- (!u.children) coordinate (B) -- (!ul.parent) coordinate (C) pic[fill=drawColor, angle radius=\\angleSize]{angle};"
			+ lnSep + "		}	" + lnSep + "	}," + lnSep + "	/tikz/or/.style={" + lnSep + "	}," + lnSep + "	alternative/.style={" + lnSep + "		tikz+={"
			+ lnSep
			+ "			\\path (.parent) coordinate (A) -- (!u.children) coordinate (B) -- (!ul.parent) coordinate (C) pic[draw=drawColor, angle radius=\\angleSize]{angle};"
			+ lnSep + "		}	" + lnSep + "	}," + lnSep + "	/tikz/alternative/.style={" + lnSep + "	}," + lnSep + "	/tikz/placeholder/.style={" + lnSep
			+ "	}," + lnSep + "	collapsed/.style={" + lnSep + "		rounded corners," + lnSep + "		no edge," + lnSep + "		for tree={" + lnSep
			+ "			fill opacity=0," + lnSep + "			draw opacity=0," + lnSep + "			l = 0em," + lnSep + "		}" + lnSep + "	}," + lnSep
			+ "	/tikz/hiddenNodes/.style={" + lnSep + "		midway," + lnSep + "		rounded corners," + lnSep + "		draw=drawColor," + lnSep
			+ "		fill=white," + lnSep + "		minimum size = 1.2em," + lnSep + "		minimum width = 0.8em," + lnSep + "		scale=0.9" + lnSep + "	},"
			+ lnSep + "}" + lnSep + "%-------------------------------------------------------------------------------" + lnSep);
	}

	private static void printBody(StringBuilder str, String FileName) {
		str.append("\\input{head.tex}" + lnSep); // Include head
		str.append("\\begin{document}" + lnSep + "	");
		str.append("\\sffamily" + lnSep);
		str.append("	\\input{" + FileName + "}" + lnSep); // Include main
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

	private static void printLegend(StringBuilder str, boolean legendHidden) {
		if (!legendHidden) {
			boolean check = false;
			final StringBuilder myString = new StringBuilder();
			if (legend[0]) {
				check = true;
				myString.append("		\\node [abstract,label=right:Abstract] {}; \\\\" + lnSep);
				legend[0] = false;
			}
			if (legend[1]) {
				check = true;
				myString.append("		\\node [concrete,label=right:Concrete] {}; \\\\" + lnSep);
				legend[1] = false;
			}
			if (legend[2]) {
				check = true;
				myString.append("		\\node [mandatory,label=right:Mandatory] {}; \\\\" + lnSep);
				legend[2] = false;
			}
			if (legend[3]) {
				check = true;
				myString.append("		\\node [optional,label=right:Optional] {}; \\\\" + lnSep);
				legend[3] = false;
			}
			if (legend[4]) {
				check = true;
				// myString.append(" \\filldraw[drawColor] (0.45,0.15) ++ (225:0.3) arc[start angle=315,end angle=225,radius=0.2]; " + lnSep
				// + " \\node [or,label=right:Or] {}; \\\\" + lnSep);
				myString.append("			\\filldraw[drawColor] (0.1,0) - +(-0,-0.2) - +(0.2,-0.2)- +(0.1,0);" + lnSep
					+ "			\\draw[drawColor] (0.1,0) -- +(-0.2, -0.4);" + lnSep + "			\\draw[drawColor] (0.1,0) -- +(0.2,-0.4);" + lnSep
					+ "			\\fill[drawColor] (0,-0.2) arc (240:300:0.2);" + lnSep + "		\\node [or,label=right:Or] {}; \\\\");
				legend[4] = false;
			}
			if (legend[5]) {
				check = true;
				// myString.append(" \\draw[drawColor] (0.45,0.15) ++ (225:0.3) arc[start angle=315,end angle=225,radius=0.2] -- cycle; " + lnSep
				// + " \\node [alternative,label=right:Alternative] {}; \\\\" + lnSep);
				myString.append("			\\draw[drawColor] (0.1,0) -- +(-0.2, -0.4);" + lnSep + "			\\draw[drawColor] (0.1,0) -- +(0.2,-0.4);"
					+ lnSep + "			\\draw[drawColor] (0,-0.2) arc (240:300:0.2);" + lnSep + "		\\node [alternative,label=right:Alternative] {}; \\\\");
				legend[5] = false;
			}
			if (legend[6]) {
				check = true;
				myString.append("		\\node [hiddenNodes,label=center:1,label=right:Collapsed Nodes] {}; \\\\" + lnSep);
				legend[6] = false;
			}
			if (check) {
				str.append("	\\matrix [anchor=north west] at (current bounding box.north east) {" + lnSep + "		\\node [placeholder] {}; \\\\" + lnSep
					+ "	};" + lnSep + "	\\matrix [draw=drawColor,anchor=north west] at (current bounding box.north east) {" + lnSep
					+ "		\\node [label=center:\\underline{Legend:}] {}; \\\\" + lnSep);
				str.append(myString);
				str.append("	};" + lnSep);
				check = false;
			} else {
				for (int i = 0; i < legend.length; ++i) {
					legend[i] = false;
				}
				check = false;
			}
		}
	}

	/**
	 * Writes the converted feature diagram with all required packages and styles (for the tex format) in a String.
	 *
	 * @param object The graphic feature model
	 * @return LaTeX Code as String
	 */
	@Override
	public String write(IGraphicalFeatureModel object) {
		final StringBuilder str = new StringBuilder();
		printHead(str);
		str.append("\\begin{document}" + lnSep + "	%---The Feature Diagram-----------------------------------------------------" + lnSep + "	\\begin{forest}"
			+ lnSep + "		featureDiagram" + lnSep);

		StringBuilder myTree = new StringBuilder();
		str.append("		");
		printTree(getRoot(object), object, myTree);
		myTree = postProcessing(myTree);
		str.append(myTree);
		str.append(lnSep);
		printLegend(str, object.isLegendHidden());
		str.append("	\\end{forest}" + lnSep + "	%---------------------------------------------------------------------------" + lnSep + "\\end{document}");
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

	/**
	 * Return the suffix of the extension.
	 *
	 * @return the suffix of the extension
	 */
	@Override
	public String getSuffix() {
		return ".tex";
	}

	/**
	 * Returns the name/description of the extension as a string.
	 *
	 * @return the name/description of the extension
	 */
	@Override
	public String getName() {
		return "LaTeX-Document with TikZ";
	}

	@Override
	public String getId() {
		return ID;
	}

}
