/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
		String name = getMethodName(terminal);
		
		String modifiers = terminal.getBody().substring(0, terminal.getBody().indexOf(name));

		// add method
		addMethod(name, getMethodParameter(terminal), "void", modifiers, terminal.getBody(), terminal.beginLine, terminal.endLine, true);
	}

	private String[] modifier = {"static","final","private","public","protected"};
	
	public void caseFieldDeclaration(FSTTerminal terminal) {
		LinkedList<String> fields = getFields(terminal.getBody());
		for (int i = 2;i < fields.size();i++) {
			// add field
			FSTField field = new FSTField(fields.get(i), fields.get(1), 0, fields.get(0), terminal.getBody(), terminal.beginLine, terminal.endLine);
			field.setOwn(modelBuilder.getCurrentFile());
			modelBuilder.getCurrentClass().add(field);
		}
	}
	
	/**
	 * 
	 * @param terminal body
	 * @return list(0) field modifiers
	 * 		   list(1) field type
	 * 		   ... field names
	 */
	public LinkedList<String> getFields(String body) {
		String modifiers = "";
		StringBuilder type = new StringBuilder();
		StringBuilder namesBuilder = new StringBuilder();
		boolean mod = false;
		boolean t1 = false;
		boolean t2 = false;
		
		// removing comments
		while (body.contains("/*") && body.contains("*/")) {
			body = body.substring(0, body.indexOf("/*")) 
					+ " " + body.substring(body.indexOf("*/") + 2);
		}
		
		while (body.contains("  ")) {
			body = body.replace("  ", " ");
		}
		
		for (String s : body.split(" ")) {
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
			names = names.substring(0,names.length() - 1);
		}
		
		String[] namesArray = names.split(",");
		for (int i = 0;i < namesArray.length;i++) {
			String f = namesArray[i];
			f = f.replace("\n", "");
			f = f.replace("\r", "");
			while (f.startsWith(" ")) {
				f = f.substring(1);
			}
			namesArray[i] = f;
		}
		
		LinkedList<String> field = new LinkedList<String>();
		field.add(modifiers);
		field.add(type.toString());
		for (String name : namesArray) {
			field.add(name);
		}
		return field;
	}

	private boolean isModifier(String ss) {
		for (String modifier : this.modifier) {
			if (modifier.equals(ss)) {
				return true;
			}
		}
		return false;
	}

	@Override
	void caseMethodDeclaration(FSTTerminal terminal) {
		// get name
		String name = getMethodName(terminal);
		
		// get return type
		String body = terminal.getBody().substring(0, terminal.getBody().indexOf(name));
		String returnType = body.split("[ ]")[body.split("[ ]").length -1];
		
		// get modifiers
		String modifiers = "";
		if (body.indexOf(returnType) != 0) {
			modifiers = body.substring(0, body.indexOf(returnType)-1);
		}

		// add method
		addMethod(name, getMethodParameter(terminal), returnType, modifiers, terminal.getBody(), terminal.beginLine, terminal.endLine, false);
	}
	
	/**
	 * @param terminal
	 * @return
	 */
	private String getMethodName(FSTTerminal terminal) {
		String name = terminal.getBody().substring(0, terminal.getBody().indexOf('('));
		while (name.endsWith(" ")) {
			name = name.substring(0,name.length() - 1);
		}
		return name.substring(name.lastIndexOf(' ') + 1);
	}

	private LinkedList<String> getMethodParameter(FSTTerminal terminal) {
		String parameter = terminal.getBody().substring(
				terminal.getBody().indexOf('(') + 1, terminal.getBody().indexOf(')'));
		LinkedList<String> parameterTypes = new LinkedList<String>();
		if (!parameter.equals("") && !parameter.startsWith("{")) {
			String[] p = parameter.split("[-]");
			for (int i = 0; i < p.length; i+=2) {
				parameterTypes.add(p[i]);
			}
		}
		return parameterTypes;
	}
}
