/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
import de.ovgu.featureide.core.fstmodel.FSTMethod;

/**
 * @author Jens Meinicke
 */
public class JavaClassBuilder extends ClassBuilder{

	public JavaClassBuilder(FeatureHouseModelBuilder builder) {
		super(builder);
	}

	private String[] modifier = {"static","final","private","public","protected"};
	
	public void caseFieldDeclaration(FSTTerminal terminal) {
		LinkedList<String> fields = getFields(terminal.getBody());
		for (int i = 2;i < fields.size();i++) {
			// add field
			FSTField field = new FSTField(fields.get(i), fields.get(1), 0, fields.get(0));
			field.setOwn(modelBuilder.getCurrentFile());
			modelBuilder.getCurrentClass().fields.put(field.getIdentifier(), field);
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
		String type = "";
		String names = "";
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
					names += s.split("[=]")[0];
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
				type += s;
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
				type += s;
				if (s.contains(">")) {
					t2 = false;
				}
			} else {
				// case: name(s)
				names += s;
			}
		}
		
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
		field.add(type);
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
	
	public void caseMethodDeclaration(FSTTerminal terminal) {
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
		addMethod(name, getMethodParameter(terminal), returnType, modifiers);
	}

	public void caseConstructorDeclaration(FSTTerminal terminal) {
		// get name
		String name = getMethodName(terminal);
		
		// get modifiers
		String modifiers = "";
		if (terminal.getBody().indexOf(name) > 0) {
			modifiers = terminal.getBody().substring(0, terminal.getBody().indexOf(name) - 1);
		}

		// add constructor
		addMethod(name, getMethodParameter(terminal), "void", modifiers);
	}
	
	private String getMethodName(FSTTerminal terminal) {
		return terminal.getName().substring(0, terminal.getName().indexOf("("));
	}
	
	private LinkedList<String> getMethodParameter(FSTTerminal terminal) {
		String parameter = terminal.getName().substring(
				terminal.getName().indexOf("(") + 1, terminal.getName().indexOf(")"));
		LinkedList<String> parameterTypes = new LinkedList<String>();
		if (!parameter.equals("") && !parameter.startsWith("{")) {
			String[] p = parameter.split("[-]");
			for (int i = 0; i < p.length; i+=2) {
				parameterTypes.add(p[i]);
			}
		}
		return parameterTypes;
	}
	
	private void addMethod(String name, LinkedList<String> parameterTypes, 
			String returnType, String modifiers) {
		FSTMethod method = new FSTMethod(name, parameterTypes, returnType, modifiers);								
		method.setOwn(modelBuilder.getCurrentFile());
		modelBuilder.getCurrentClass().methods.put(method.getIdentifier(), method);
	}
}
