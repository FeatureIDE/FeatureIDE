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
package de.ovgu.featureide.fm.ui.editors.configuration;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.io.APersistentFormat;
import de.ovgu.featureide.fm.ui.editors.elements.TikzFormat;

/**
 * Converts the configuration (advanced configuration) in a LaTeX format. This class implements a LaTeX converter for the advanced configuration of a Feature
 * Diagram. <br> The main class uses one String for the latex code; the subclasses divides the code into three different Strings (each subclass for one String).
 *
 * @author Simon Wenk
 * @author Yang Liu
 */
public class LatexFormat extends APersistentFormat<Configuration> {

	public static final String ID = PluginID.PLUGIN_ID + "format.fm" + LatexFormat.class.getSimpleName();
	public static final String LATEX_DOCUMENT = ".tex";
	public static final String LATEX_DOCUMENT_DESCRIPTION = "LaTeX Document";

	private static final String lnSep = System.lineSeparator();

	/**
	 * Creates the styles and packages that are required for the converted configuration. <br> <br> <b>Note:</b> For exporting purposes the file name must be
	 * <i> head.tex </i> and exported in the same folder as the main file.
	 */
	public static class LaTeXHead extends APersistentFormat<Configuration> {

		/**
		 * Writes the required styles and packages in a String.
		 *
		 * @param config The configuration of a Feature Model
		 * @return LaTeX Code as a String
		 */
		@Override
		public String write(Configuration config) {
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
			return LATEX_DOCUMENT;
		}

		@Override
		public String getName() {
			return LATEX_DOCUMENT_DESCRIPTION;
		}

		@Override
		public String getId() {
			return ID;
		}

	}

	/**
	 * Creates the main file. This contains the converted configuration. <br> </br>
	 *
	 * <b> Note: </b> The class <i> LaTeXHead </i> creates the styles and packages that are required to execute the resulting LaTeX Code correctly.
	 *
	 * @see {LaTeXHead}
	 */
	public static class LaTeXMain extends APersistentFormat<Configuration> {

		/**
		 * Writes the structure of the configuration in tex-format.
		 *
		 * @param config The configuration of a Feature Model
		 * @return LaTeX Code as a String
		 */
		@Override
		public String write(Configuration config) {
			StringBuilder str = new StringBuilder();
			printRoot(config, config.getRoot().getFeature(), str, 0);
			str = TikzFormat.postProcessing(str);
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
			return LATEX_DOCUMENT;
		}

		@Override
		public String getName() {
			return LATEX_DOCUMENT_DESCRIPTION;
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
	public static class LaTeXBody extends APersistentFormat<Configuration> {

		String fileName = new String();

		/**
		 * @param FileName The file name of the main file
		 */
		public LaTeXBody(String fileName) {
			this.fileName = fileName;
		}

		/**
		 * Constructs the body of the LaTeX file, includes the head file and the main file and writes it in a String.
		 *
		 * @param config The configuration of a Feature Model
		 * @return LaTeX Code as a String
		 */
		@Override
		public String write(Configuration config) {
			final StringBuilder str = new StringBuilder();
			printBody(str, fileName);
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
			return LATEX_DOCUMENT;
		}

		@Override
		public String getName() {
			return LATEX_DOCUMENT_DESCRIPTION;
		}

		@Override
		public String getId() {
			return ID;
		}

	}

	private static void printHead(StringBuilder str) {
		str.append("\\documentclass[varwidth,convert,border=5pt]{standalone}" + lnSep + "\\usepackage{amsmath}" + lnSep + "\\usepackage{tikz}" + lnSep
			+ "\\usepackage{color}" + lnSep + "\\definecolor{boxColor}{RGB}{192 192 192}" + lnSep + "\\definecolor{plusColor}{RGB}{48 191 48}" + lnSep
			+ "\\definecolor{minusColor}{HTML}{be0105}" + lnSep + "\\newcommand\\tab[1][1em]{\\hspace*{#1}}" + lnSep + lnSep
			+ "\\newcommand{\\myPlus}{\\ \\fcolorbox{black}{boxColor}{\\color{plusColor}$\\boldsymbol{\\pmb{+}}$}\\ }" + lnSep
			+ "\\newcommand{\\myPlusblank}{\\ \\fcolorbox{black}{white}{\\color{plusColor}$\\boldsymbol{\\pmb{+}}$}\\ }" + lnSep
			+ "\\newcommand{\\myMinus}{\\ \\fcolorbox{black}{boxColor}{\\color{minusColor}$\\boldsymbol{\\pmb{-}}$}\\ }" + lnSep
			+ "\\newcommand{\\myMinusblank}{\\ \\fcolorbox{black}{white}{\\color{minusColor}$\\boldsymbol{\\pmb{-}}$}\\ }" + lnSep
			+ "\\newcommand{\\myBox}{\\ \\fcolorbox{black}{white}{\\color{white}$\\boldsymbol{\\pmb{+}}$}\\ }" + lnSep + lnSep
			+ "\\newcommand{\\optional}{$\\mspace{5mu}\\mathord{\\begin{tikzpicture}[scale=0.17]" + lnSep + "\\draw (0,0) circle[radius=1em];" + lnSep
			+ "\\draw[opacity = 0] (0em,0em) -- (0em,-1.9em);" + lnSep + "\\draw[opacity = 0] (-1.94em,0em) -- (1.94em,0em);" + lnSep + "\\end{tikzpicture}}$}"
			+ lnSep + "\\newcommand{\\mandatory}{$\\mspace{5mu}\\mathord{\\begin{tikzpicture}[scale=0.17]" + lnSep
			+ "\\draw[fill=black] (0,0) circle[radius=1em];" + lnSep + "\\draw[opacity = 0] (0em,0em) -- (0em,-1.9em);" + lnSep
			+ "\\draw[opacity = 0] (-1.94em,0em) -- (1.94em,0em);" + lnSep + "\\end{tikzpicture}}$}" + lnSep + lnSep
			+ "\\newcommand{\\fold}{$\\mathord{\\begin{tikzpicture}[scale=0.15]" + lnSep + "\\fill (-1em,1em) -- (1em,0em) -- (-1em,-1em) -- cycle;" + lnSep
			+ "\\draw[opacity = 0] (0em,0em) -- (0em,-2.2em);" + lnSep + "\\end{tikzpicture}}$}" + lnSep
			+ "\\newcommand{\\unfold}{$\\mathord{\\begin{tikzpicture}[scale=0.15]" + lnSep + "\\fill (0em,-1em) -- (-1em,1em) -- (1em,1em) -- cycle;" + lnSep
			+ "\\draw[opacity = 0] (0em,0em) -- (0em,-2.2em);" + lnSep + "\\end{tikzpicture}}$}" + lnSep
			+ "\\newcommand{\\nofold}{$\\mathord{\\begin{tikzpicture}[scale=0.15]" + lnSep
			+ "\\fill[opacity = 0] (0em,-1em) -- (-1em,1em) -- (1em,1em) -- cycle;" + lnSep + "\\draw[opacity = 0] (0em,0em) -- (0em,-2.2em);" + lnSep
			+ "\\end{tikzpicture}}$}" + lnSep + lnSep + "\\newcommand{\\myOr}{$\\mspace{5mu}\\mathord{\\begin{tikzpicture}[scale=2.2]" + lnSep
			+ "        \\filldraw (0.1em,0em) - +(0.025em,-0.15em) - +(0.175em,-0.15em)- +(0.1em,0em);" + lnSep
			+ "        \\draw (0.1em,0em) -- +(-0.15em, -0.3em);" + lnSep + "        \\draw (0.1em,0em) -- +(0.15em,-0.3em);" + lnSep
			+ "        \\filldraw (0.025em,-0.15em) arc (240:300:0.15em);" + lnSep + "    \\end{tikzpicture}}$}" + lnSep
			+ "\\newcommand{\\Alternative}{$\\mspace{5mu}\\mathord{\\begin{tikzpicture}[scale=2.2]" + lnSep
			+ "        \\draw (0.1em,0em) -- +(-0.15em, -0.3em);" + lnSep + "        \\draw (0.1em,0em) -- +(0.15em,-0.3em);" + lnSep
			+ "        \\draw (0.025em,-0.15em) arc (240:300:0.15em);" + lnSep + "    \\end{tikzpicture}}$}" + lnSep + "    " + lnSep
			+ "\\newcommand{\\blank}{$\\mspace{5mu}\\mathord{\\begin{tikzpicture}[scale=0.17]" + lnSep + "\\draw[opacity = 0] (-1.94em,0em) -- (1.94em,0em);"
			+ lnSep + "\\end{tikzpicture}}$}");
	}

	private static void printBody(StringBuilder str, String fileName) {
		str.append(
				"\\input{head.tex}" + lnSep + "\\begin{document}" + lnSep + "	\\sffamily" + lnSep + "	\\input{" + fileName + "}" + lnSep + "\\end{document}");
	}

	private static void printTabs(StringBuilder str, int depth) {
		for (int i = depth; i > 0; --i) {
			str.append("\\tab");
		}
	}

	private static void printRoot(Configuration config, IFeature node, StringBuilder tree, int depth) {
		tree.append("\\fboxsep0.1mm" + lnSep + "\\noindent" + lnSep);
		printStructure(node, tree);
		printAttributs(node, tree);
		printConfiguration(config, node, tree);
		printNodeName(config, node, tree);
		getChildren(config, node, tree, depth);
	}

	private static void printNode(Configuration config, IFeature node, StringBuilder tree, int depth) {
		printTabs(tree, depth);
		printStructure(node, tree);
		printAttributs(node, tree);
		printConfiguration(config, node, tree);
		printNodeName(config, node, tree);
		getChildren(config, node, tree, depth);
	}

	private static void getChildren(Configuration config, IFeature node, StringBuilder tree, int depth) {
		if (node.getStructure().hasChildren()) {
			final List<IFeatureStructure> myChildren = node.getStructure().getChildren();
			for (int i = 0; i < myChildren.size(); ++i) {
				printNode(config, myChildren.get(i).getFeature(), tree, depth + 1);
			}
		}
	}

	private static void printStructure(IFeature node, StringBuilder tree) {
		if (node.getStructure().hasChildren()) {
			tree.append("\\unfold");
		} else {
			tree.append("\\nofold");
		}
	}

	private static void printAttributs(IFeature node, StringBuilder tree) {
		if ((node.getStructure().isRoot() == false)) {
			if (node.getStructure().getParent().isAnd() == true) {
				if (node.getStructure().isMandatory()) {
					tree.append("\\mandatory");
				} else {
					tree.append("\\optional");
				}
			} else if (node.getStructure().getParent().isAlternative()) {
				tree.append("\\Alternative");
			} else if (node.getStructure().getParent().isOr()) {
				tree.append("\\myOr");
			}
		} else {
			tree.append("\\blank");
		}
	}

	private static void printConfiguration(Configuration config, IFeature node, StringBuilder tree) {
		_printConfiguration(config.getSelectablefeature(node.getName()), tree);
	}

	private static void _printConfiguration(SelectableFeature node, StringBuilder tree) {
		if (node.getAutomatic() == Selection.SELECTED) {
			tree.append("\\myPlus");
		} else if (node.getAutomatic() == Selection.UNSELECTED) {
			tree.append("\\myMinus");
		} else if (node.getManual() == Selection.SELECTED) {
			tree.append("\\myPlusblank");
		} else if (node.getManual() == Selection.UNSELECTED) {
			tree.append("\\myMinusblank");
		} else {
			tree.append("\\myBox");
		}
	}

	private static void printNodeName(Configuration config, IFeature node, StringBuilder tree) {
		_printNodeName(config.getSelectablefeature(node.getName()), tree);
	}

	/**
	 * Calculates in which color the node name has to be print and does this. Only by open clauses the color of the name is blue (to much selected) or green
	 * (not enough selected). In all other cases it is the normal color.
	 *
	 * @param node The Feature to be processed
	 * @param tree The StringBuilder that uses LaTeXMain to build the main code
	 */
	private static void _printNodeName(SelectableFeature node, StringBuilder tree) {
		if (node.getOpenClauses().size() > 0) {
			final Collection<Node> myOpenClauses = node.getOpenClauses();
			final StringBuilder myOpenFeatures = new StringBuilder();
			final List<String> myOpenFeaturesList = new ArrayList<String>();
			for (final Node myClause : myOpenClauses) {
				myOpenFeatures.append(myClause.toString() + " |");
			}

			for (int i = 0, begin = 0, end = 0; i < myOpenFeatures.length(); ++i) {
				if (myOpenFeatures.charAt(i) == '|') {
					end = i - 1;
					myOpenFeaturesList.add(myOpenFeatures.substring(begin, end));
					begin = i + 2;
				}
			}
			for (final String myFeature : myOpenFeaturesList) {
				if (node.getName().equals(myFeature)) {
					tree.append("\\textbf{\\color{plusColor}" + node.getName() + "}\\\\" + lnSep);
				} else if (("-" + node.getName()).equals(myFeature)) {
					tree.append("\\textbf{\\color{blue}" + node.getName() + "}\\\\" + lnSep);
				}
			}
		} else {
			tree.append(" " + node.getName() + "\\\\" + lnSep);
		}
	}

	/**
	 * Writes the converted advanced configuration with all required packages and styles (for the tex format) in a String.
	 *
	 * @param config The configuration of a Feature Model
	 * @return LaTeX Code as a String
	 */
	@Override
	public String write(Configuration config) {
		StringBuilder str = new StringBuilder();
		printHead(str);
		str.append(lnSep);
		str.append("\\begin{document}");
		str.append(lnSep);
		str.append("\\sffamily");
		printRoot(config, config.getRoot().getFeature(), str, 0);
		str = TikzFormat.postProcessing(str);
		str.append(lnSep);
		str.append("\\end{document}");

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
		return LATEX_DOCUMENT;
	}

	/**
	 * Returns the name/description of the extension as a string.
	 *
	 * @return the name/description of the extension
	 */
	@Override
	public String getName() {
		return LATEX_DOCUMENT_DESCRIPTION;
	}

	@Override
	public String getId() {
		return ID;
	}

}
