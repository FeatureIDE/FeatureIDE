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
package de.ovgu.featureide.featurehouse.model;

import java.util.LinkedList;

import de.ovgu.cide.fstgen.ast.FSTTerminal;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTModel;

/**
 * Builds Classes for the {@link FSTModel} for <code>FeatureHouse</code> Haskell files.
 *
 * @see ClassBuilder
 * @author Jens Meinicke
 */
public class HaskellClassBuilder extends ClassBuilder {

	public HaskellClassBuilder(FeatureHouseModelBuilder modelBuilder) {
		super(modelBuilder);
	}

	@Override
	void caseFieldDeclaration(FSTTerminal terminal) {
		final FSTField field = new FSTField(terminal.getBody(), "", "", terminal.getBody(), terminal.beginLine, terminal.endLine);
		modelBuilder.getCurrentClassFragment().add(field);
	}

	@Override
	void caseMethodDeclaration(FSTTerminal terminal) {
		if (!terminal.getBody().contains("::")) {
			return;
		}
		final LinkedList<String> method = getMethod(terminal.getBody());
		if (method == null) {
			return;
		}
		final LinkedList<String> parameter = new LinkedList<String>();
		parameter.add(method.get(1));
		addMethod(method.get(0), parameter, "void", "", terminal.getBody(), terminal.beginLine, terminal.endLine, false);
	}

	/**
	 *
	 * @param terminal body
	 * @return list(0) method name list(1) method type
	 */
	public LinkedList<String> getMethod(String body) {
		final LinkedList<String> method = new LinkedList<String>();
		String name = body.substring(0, body.indexOf("::"));
		while (name.endsWith(" ")) {
			name = name.substring(0, name.length() - 1);
		}
		if (name.contains(" ")) {
			return null;
		}
		method.add(name);

		String parameter = body.substring(body.indexOf("::") + 2);
		parameter = parameter.replaceAll("\n", " ");
		while (parameter.startsWith(" ")) {
			parameter = parameter.substring(1);
		}
		while (parameter.endsWith(" ")) {
			parameter = parameter.substring(0, parameter.length() - 1);
		}
		while (parameter.contains("  ")) {
			parameter = parameter.replaceAll("  ", " ");
		}
		method.add(parameter);
		return method;
	}
}
