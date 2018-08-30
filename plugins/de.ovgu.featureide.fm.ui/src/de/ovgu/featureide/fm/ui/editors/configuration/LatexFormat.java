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

import java.util.List;

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.io.APersistentFormat;
import de.ovgu.featureide.fm.ui.editors.elements.TikzFormat;

/**
 * TODO description
 *
 * @author Simon Wenk
 * @author Yang Liu
 */
public class LatexFormat extends APersistentFormat<Configuration> {

	public static final String ID = PluginID.PLUGIN_ID + "format.fm" + LatexFormat.class.getSimpleName();
	public static final String LATEX_DOCUMENT = ".tex";
	public static final String LATEX_DOCUMENT_DESCRIPTION = "LaTeX Document";

	public static class LaTeXHead extends APersistentFormat<Configuration> {

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
			// TODO
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

	public static class LaTeXMain extends APersistentFormat<Configuration> {

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

	public static class LaTeXBody extends APersistentFormat<Configuration> {

		String fileName = new String();

		public LaTeXBody(String fileName) {
			this.fileName = fileName;
		}

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
		str.append("\\documentclass[varwidth,convert,border=5pt]{standalone}\n" + "\\usepackage{amsmath}\n" + "\\usepackage{tikz}\n" + "\\usepackage{color}\n"
			+ "\\definecolor{boxColor}{RGB}{192 192 192}\n" + "\\definecolor{plusColor}{RGB}{48 191 48}\n" + "\\definecolor{minusColor}{HTML}{be0105}\n"
			+ "\\newcommand\\tab[1][1em]{\\hspace*{#1}}\n" + "\n"
			+ "\\newcommand{\\myPlus}{\\ \\fcolorbox{black}{boxColor}{\\color{plusColor}$\\boldsymbol{\\pmb{+}}$}\\ }\n"
			+ "\\newcommand{\\myPlusblank}{\\ \\fcolorbox{black}{white}{\\color{plusColor}$\\boldsymbol{\\pmb{+}}$}\\ }\n"
			+ "\\newcommand{\\myMinus}{\\ \\fcolorbox{black}{boxColor}{\\color{minusColor}$\\boldsymbol{\\pmb{-}}$}\\ }\n"
			+ "\\newcommand{\\myMinusblank}{\\ \\fcolorbox{black}{white}{\\color{minusColor}$\\boldsymbol{\\pmb{-}}$}\\ }\n"
			+ "\\newcommand{\\myBox}{\\ \\fcolorbox{black}{white}{\\color{white}$\\boldsymbol{\\pmb{+}}$}\\ }\n" + "\n"
			+ "\\newcommand{\\optional}{$\\mspace{5mu}\\mathord{\\begin{tikzpicture}[scale=0.17]\n" + "\\draw (0,0) circle[radius=1em];\n"
			+ "\\draw[opacity = 0] (0em,0em) -- (0em,-1.9em);\n" + "\\draw[opacity = 0] (-1.94em,0em) -- (1.94em,0em);\n" + "\\end{tikzpicture}}$}\n"
			+ "\\newcommand{\\mandatory}{$\\mspace{5mu}\\mathord{\\begin{tikzpicture}[scale=0.17]\n" + "\\draw[fill=black] (0,0) circle[radius=1em];\n"
			+ "\\draw[opacity = 0] (0em,0em) -- (0em,-1.9em);\n" + "\\draw[opacity = 0] (-1.94em,0em) -- (1.94em,0em);\n" + "\\end{tikzpicture}}$}\n" + "\n"
			+ "\\newcommand{\\fold}{$\\mathord{\\begin{tikzpicture}[scale=0.15]\n" + "\\fill (-1em,1em) -- (1em,0em) -- (-1em,-1em) -- cycle;\n"
			+ "\\draw[opacity = 0] (0em,0em) -- (0em,-2.2em);\n" + "\\end{tikzpicture}}$}\n"
			+ "\\newcommand{\\unfold}{$\\mathord{\\begin{tikzpicture}[scale=0.15]\n" + "\\fill (0em,-1em) -- (-1em,1em) -- (1em,1em) -- cycle;\n"
			+ "\\draw[opacity = 0] (0em,0em) -- (0em,-2.2em);\n" + "\\end{tikzpicture}}$}\n"
			+ "\\newcommand{\\nofold}{$\\mathord{\\begin{tikzpicture}[scale=0.15]\n" + "\\fill[opacity = 0] (0em,-1em) -- (-1em,1em) -- (1em,1em) -- cycle;\n"
			+ "\\draw[opacity = 0] (0em,0em) -- (0em,-2.2em);\n" + "\\end{tikzpicture}}$}\n" + "\n"
			+ "\\newcommand{\\myOr}{$\\mspace{5mu}\\mathord{\\begin{tikzpicture}[scale=2.2]\n"
			+ "        \\filldraw (0.1em,0em) - +(0.025em,-0.15em) - +(0.175em,-0.15em)- +(0.1em,0em);\n"
			+ "        \\draw (0.1em,0em) -- +(-0.15em, -0.3em);\n" + "        \\draw (0.1em,0em) -- +(0.15em,-0.3em);\n"
			+ "        \\filldraw (0.025em,-0.15em) arc (240:300:0.15em);\n" + "    \\end{tikzpicture}}$}\n"
			+ "\\newcommand{\\Alternative}{$\\mspace{5mu}\\mathord{\\begin{tikzpicture}[scale=2.2]\n" + "        \\draw (0.1em,0em) -- +(-0.15em, -0.3em);\n"
			+ "        \\draw (0.1em,0em) -- +(0.15em,-0.3em);\n" + "        \\draw (0.025em,-0.15em) arc (240:300:0.15em);\n" + "    \\end{tikzpicture}}$}\n"
			+ "    \n" + "\\newcommand{\\blank}{$\\mspace{5mu}\\mathord{\\begin{tikzpicture}[scale=0.17]\n"
			+ "\\draw[opacity = 0] (-1.94em,0em) -- (1.94em,0em);\n" + "\\end{tikzpicture}}$}");
	}

	private static void printBody(StringBuilder str, String fileName) {
		str.append("\\input{head.tex}\n" + "\\begin{document}\n" + "	\\sffamily\n" + "   \\input{" + fileName + "}\n" + "\\end{document}");
	}

	private static void printTabs(StringBuilder str, int depth) {
		for (int i = depth; i > 0; --i) {
			str.append("\\tab");
		}
	}

	private static void printRoot(Configuration config, IFeature node, StringBuilder tree, int depth) {
		// TODO: Implementation
		tree.append("\\fboxsep0.1mm\n\\noindent\n");
		printStructure(node, tree);
		printAttributs(node, tree);
		printConfiguration(config, node, tree);
		printNodeName(config, node, tree);
		getChildren(config, node, tree, depth);
	}

	private static void printNode(Configuration config, IFeature node, StringBuilder tree, int depth) {
		// TODO: Implementation
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

	private static void _printNodeName(SelectableFeature node, StringBuilder tree) {
		if (node.getOpenClauses().size() > 0) {
			tree.append("\\textbf{\\color{plusColor}" + node.getName() + "}\\\\\n");
		} else {
			tree.append(" " + node.getName() + "\\\\\n");
		}
	}

	@Override
	public String write(Configuration config) {
		StringBuilder str = new StringBuilder();
		printHead(str);
		str.append("\n");
		str.append("\\begin{document}\n");
		str.append("\\sffamily");
		printRoot(config, config.getRoot().getFeature(), str, 0);
		str = TikzFormat.postProcessing(str);
		str.append("\n\\end{document}");

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
