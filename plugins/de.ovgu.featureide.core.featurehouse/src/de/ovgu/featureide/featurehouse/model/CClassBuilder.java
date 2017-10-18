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
 * Builds Classes for the FSTModel for <code>FeatureHouse</code> C files.
 *
 * @see ClassBuilder
 * @author Jens Meinicke
 */
public class CClassBuilder extends ClassBuilder {

	private final String[] modifier = { "static" };

	public CClassBuilder(FeatureHouseModelBuilder modelBuilder) {
		super(modelBuilder);
	}

	@Override
	void caseConstructorDeclaration(FSTTerminal terminal) {

	}

	@Override
	void caseFieldDeclaration(FSTTerminal terminal) {
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
		final LinkedList<String> fields = new LinkedList<String>();
		String modifiers = "";
		String type = "";
		final StringBuilder nameBuilder = new StringBuilder();
		while (body.contains(" ,")) {
			body = body.replaceAll(" ,", ",");
		}
		while (body.contains(", ")) {
			body = body.replaceAll(", ", ",");
		}
		while (body.contains(" ;")) {
			body = body.replaceAll(" ;", ";");
		}
		boolean mod = false;
		for (final String s : body.split("[ ]")) {
			if (!mod && isModifier(s)) {
				if (modifiers.equals("")) {
					modifiers = s;
				} else {
					modifiers = modifiers + " " + s;
				}
			} else if (!s.contains(";")) {
				mod = true;
				if (type.equals("")) {
					type = s;
				} else {
					type = type + " " + s;
				}
			} else {
				nameBuilder.append(s);
			}
		}
		fields.add(modifiers);
		fields.add(type);
		final String names = nameBuilder.toString().replaceAll(";", "");
		for (final String name : names.split("[,]")) {
			fields.add(name);
		}
		return fields;
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
		final LinkedList<String> method = getMethod(terminal.getBody());
		final LinkedList<String> parameterTypes = new LinkedList<String>();
		for (int i = 3; i < method.size(); i++) {
			parameterTypes.add(method.get(i));
		}
		addMethod(method.get(0), parameterTypes, method.get(1), method.get(2), terminal.getBody(), terminal.beginLine, terminal.endLine, false);
	}

	/**
	 * @param method body
	 * @return list(0): name list(1): return type list(2): modifiers ...: parameter types
	 *
	 */
	public LinkedList<String> getMethod(String body) {
		final LinkedList<String> method = new LinkedList<String>();

		String name = body.substring(0, body.indexOf('('));
		name = name.replaceAll("\n", " ");
		while (name.endsWith(" ")) {
			name = name.substring(0, name.length() - 1);
		}
		name = name.substring(name.lastIndexOf(' ') + 1);
		method.add(name);

		String returnType = body.substring(0, body.indexOf(name));
		returnType = returnType.replaceAll("\n", "");
		final StringBuilder modifiers = new StringBuilder();
		for (final String m : modifier) {
			if (returnType.contains(m)) {
				returnType = returnType.replaceAll(m + " ", "");
				modifiers.append(m + " ");
			}
		}
		while (returnType.startsWith(" ")) {
			returnType = returnType.substring(1);
		}
		while (returnType.endsWith(" ")) {
			returnType = returnType.substring(0, returnType.length() - 1);
		}
		method.add(returnType);
		method.add(modifiers.toString());

		final String parameter = body.substring(body.indexOf('(') + 1, body.indexOf(')'));
		final String[] params = parameter.split(",");
		for (String p : params) {
			while (p.startsWith(" ")) {
				p = p.substring(1);
			}
			method.add(p);
		}

		return method;
	}
}
