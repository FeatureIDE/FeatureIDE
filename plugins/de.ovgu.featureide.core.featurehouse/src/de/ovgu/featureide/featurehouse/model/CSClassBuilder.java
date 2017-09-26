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

/**
 * Builds Classes for the FSTModel for <code>FeatureHouse</code> CSharp files.
 *
 * @see ClassBuilder
 * @author Jens Meinicke
 */
public class CSClassBuilder extends ClassBuilder {

	/**
	 * @param modelBuilder
	 */
	public CSClassBuilder(FeatureHouseModelBuilder modelBuilder) {
		super(modelBuilder);
	}

	@Override
	void caseConstructorDeclaration(FSTTerminal terminal) {
		// get name
		final String name = getMethodName(terminal);

		final String modifiers = terminal.getBody().substring(0, terminal.getBody().indexOf(name));

		// add method
		addMethod(name, getMethodParameter(terminal), "void", modifiers, terminal.getBody(), terminal.beginLine, terminal.endLine, true);
	}

	private final String[] modifier = { "static", "final", "private", "public", "protected" };

	@Override
	public void caseFieldDeclaration(FSTTerminal terminal) {
		final LinkedList<String> fields = getFields(terminal.getBody());
		for (int i = 2; i < fields.size(); i++) {
			// add field
			final FSTField field = new FSTField(fields.get(i), fields.get(1), fields.get(0), terminal.getBody(), terminal.beginLine, terminal.endLine);
			modelBuilder.getCurrentClassFragment().add(field);
		}
	}

	/**
	 *
	 * @param terminal body
	 * @return list(0) field modifiers list(1) field type ... field names
	 */
	public LinkedList<String> getFields(String body) {
		String modifiers = "";
		final StringBuilder type = new StringBuilder();
		final StringBuilder namesBuilder = new StringBuilder();
		boolean mod = false;
		boolean t1 = false;
		boolean t2 = false;

		// removing comments
		while (body.contains("/*") && body.contains("*/")) {
			body = body.substring(0, body.indexOf("/*")) + " " + body.substring(body.indexOf("*/") + 2);
		}

		while (body.contains("  ")) {
			body = body.replace("  ", " ");
		}

		for (final String s : body.split(" ")) {
			if (s.contains("=")) {
				if (!s.startsWith("=")) {
					namesBuilder.append(s.split("[=]")[0]);
				}
				break;
			}

			if (!mod && isModifier(s)) {
				// case: modifier
				if (modifiers.equals("")) {
					modifiers = s;
				} else {
					modifiers = modifiers + " " + s;
				}
			} else if (!t1) {
				// case: type
				mod = true;
				t1 = true;
				type.append(s);
				if (s.contains("<")) {
					// case: has type arguments
					t2 = true;
					if (s.contains(">")) {
						t2 = false;
					}
				}
			} else if (t2 || s.contains("<")) {
				// case: type with type arguments
				t2 = true;
				type.append(s);
				if (s.contains(">")) {
					t2 = false;
				}
			} else {
				// case: name(s)
				namesBuilder.append(s);
			}
		}
		String names = namesBuilder.toString();
		if (names.endsWith(";") || names.endsWith("+") || names.endsWith("-")) {
			names = names.substring(0, names.length() - 1);
		}

		final String[] namesArray = names.split(",");
		for (int i = 0; i < namesArray.length; i++) {
			String f = namesArray[i];
			f = f.replace("\n", "");
			f = f.replace("\r", "");
			while (f.startsWith(" ")) {
				f = f.substring(1);
			}
			namesArray[i] = f;
		}

		final LinkedList<String> field = new LinkedList<String>();
		field.add(modifiers);
		field.add(type.toString());
		for (final String name : namesArray) {
			field.add(name);
		}
		return field;
	}

	private boolean isModifier(String ss) {
		for (final String modifier : this.modifier) {
			if (modifier.equals(ss)) {
				return true;
			}
		}
		return false;
	}

	@Override
	void caseMethodDeclaration(FSTTerminal terminal) {
		// get name
		final String name = getMethodName(terminal);

		// get return type
		final String body = terminal.getBody().substring(0, terminal.getBody().indexOf(name));
		final String returnType = body.split("[ ]")[body.split("[ ]").length - 1];

		// get modifiers
		String modifiers = "";
		if (body.indexOf(returnType) != 0) {
			modifiers = body.substring(0, body.indexOf(returnType) - 1);
		}

		// add method
		addMethod(name, getMethodParameter(terminal), returnType, modifiers, terminal.getBody(), terminal.beginLine, terminal.endLine, false);
	}

	private String getMethodName(FSTTerminal terminal) {
		String name = terminal.getBody().substring(0, terminal.getBody().indexOf('('));
		while (name.endsWith(" ")) {
			name = name.substring(0, name.length() - 1);
		}
		return name.substring(name.lastIndexOf(' ') + 1);
	}

	private LinkedList<String> getMethodParameter(FSTTerminal terminal) {
		final String parameter = terminal.getBody().substring(terminal.getBody().indexOf('(') + 1, terminal.getBody().indexOf(')'));
		final LinkedList<String> parameterTypes = new LinkedList<String>();
		if (!"".equals(parameter) && !parameter.startsWith("{")) {
			final String[] p = parameter.split("[-]");
			for (int i = 0; i < p.length; i += 2) {
				parameterTypes.add(p[i]);
			}
		}
		return parameterTypes;
	}
}
