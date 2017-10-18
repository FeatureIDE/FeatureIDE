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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.featurehouse.model;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.cide.fstgen.ast.FSTNode;
import de.ovgu.cide.fstgen.ast.FSTNonTerminal;
import de.ovgu.cide.fstgen.ast.FSTTerminal;
import de.ovgu.featureide.core.fstmodel.FSTAsmetaLDomain;
import de.ovgu.featureide.core.fstmodel.FSTAsmetaLInitialization;
import de.ovgu.featureide.core.fstmodel.FSTAstemaLFunction;
import de.ovgu.featureide.core.fstmodel.FSTInvariant;
import de.ovgu.featureide.core.fstmodel.FSTModel;

/**
 * Builds Classes for the {@link FSTModel} for <code>FeatureHouse</code> Haskel files.
 */
public class AsmetaLClassBuilder extends ClassBuilder {

	public AsmetaLClassBuilder(FeatureHouseModelBuilder modelBuilder) {
		super(modelBuilder);
	}

	@Override
	public void caseInvariant(FSTTerminal terminal) {
		final String[] type = terminal.getBody().substring(terminal.getBody().indexOf("over") + 4, terminal.getBody().indexOf(":")).trim().split(",");

		final boolean hasProperIdentifier =
			terminal.getBody().substring(terminal.getBody().indexOf("invariant") + 4, terminal.getBody().indexOf("over")).contains("inv_");

		final FSTInvariant invariant = new FSTInvariant(terminal.getName(), terminal.getBody(), new LinkedList<String>(Arrays.asList(type)), terminal.beginLine,
				terminal.endLine, hasProperIdentifier, true);
		modelBuilder.getCurrentClassFragment().add(invariant);
	}

	// Used for "Functions"
	@Override
	void caseFieldDeclaration(FSTTerminal terminal) {

		if (terminal.getType().equals("Domain")) {

			final String startTokens = "";
			final String type = "";

			final FSTAsmetaLDomain field =
				new FSTAsmetaLDomain(terminal.getName(), type, startTokens, terminal.getBody(), terminal.beginLine, terminal.endLine);
			modelBuilder.getCurrentClassFragment().add(field);
		} else if (terminal.getType().equals("Function")) {
			final String begin = terminal.getBody().substring(0, terminal.getBody().indexOf(":"));
			final String end = terminal.getBody().substring(terminal.getBody().indexOf(":") + 1);
			final String[] startTokens = begin.split(" ");
			final String name = startTokens[startTokens.length - 1];
			final String[] endTokens = end.split("->");
			final String type = endTokens[endTokens.length - 1];

			final FSTAstemaLFunction field = new FSTAstemaLFunction(name, type, startTokens[0], terminal.getBody(), terminal.beginLine, terminal.endLine);
			modelBuilder.getCurrentClassFragment().add(field);
		}
	}

	@Override
	public void caseInitialization(FSTNode node) {
		final FSTAsmetaLInitialization field = new FSTAsmetaLInitialization(node.getName(), "Initialization", "", "", 0, 0);
		modelBuilder.getCurrentClassFragment().add(field);
	}

	@Override
	public void caseSignatureDeclaration(FSTNonTerminal node) {
		final List<FSTNode> children = node.getChildren();
		for (final FSTNode child : children) {
			final FSTTerminal terminal = (FSTTerminal) child;
			final String type = child.getType();
			if (FHNodeTypes.ASMETAL_FUNCTION.equals(type)) {
				caseFieldDeclaration(terminal);
			} else if (FHNodeTypes.ASMETAL_INVARIANT.equals(type)) {
				caseInvariant(terminal);
			} else if (FHNodeTypes.ASMETAL_DOMAIN.equals(type)) {
				caseFieldDeclaration(terminal);
			}
		}
	}

	private LinkedList<String> getRuleParameter(FSTTerminal terminal) {
		final String prefix = terminal.getBody().substring(0, terminal.getBody().indexOf("="));
		if (prefix.contains("(")) {
			return new LinkedList<String>(Arrays.asList(prefix.substring(prefix.indexOf("(") + 1, prefix.indexOf(")")).split(",")));
		} else {
			return new LinkedList<String>();
		}
	}

	// Used for "Rules"
	@Override
	public void caseMethodDeclaration(FSTTerminal terminal) {
		// Rules always start with "r_"
		String name = terminal.getBody().substring(terminal.getBody().indexOf("r_"), terminal.getBody().indexOf("="));
		name = name.contains("(") ? name.substring(0, name.indexOf("(")).trim() : name.trim();
		final String returnType = terminal.getBody().indexOf("rule") == -1 ? "" : terminal.getBody().substring(0, terminal.getBody().indexOf("rule"));

		addMethod(name, getRuleParameter(terminal), returnType, "public", terminal.getBody(), terminal.beginLine, terminal.endLine, false, "", "", -1);
	}

}
