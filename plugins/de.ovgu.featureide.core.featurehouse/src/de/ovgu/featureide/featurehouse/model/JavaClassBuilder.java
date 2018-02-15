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

import de.ovgu.cide.fstgen.ast.FSTNode;
import de.ovgu.cide.fstgen.ast.FSTNonTerminal;
import de.ovgu.cide.fstgen.ast.FSTTerminal;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTInvariant;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.IRoleElement;
import de.ovgu.featureide.featurehouse.FeatureHouseCorePlugin;

/**
 * Builds Classes for the {@link FSTModel} for <code>FeatureHouse</code> Java files.
 *
 * @see ClassBuilder
 * @author Jens Meinicke
 */
public class JavaClassBuilder extends ClassBuilder {

	public JavaClassBuilder(FeatureHouseModelBuilder builder) {
		super(builder);
	}

	private final String[] modifier = { "static", "final", "private", "public", "protected", "nullable" };

	@Override
	public void caseFieldDeclaration(FSTTerminal terminal) {
		final LinkedList<String> fields = getFields(terminal.getBody());
		for (int i = 2; i < fields.size(); i++) {
			// add field
			final IRoleElement r = addField(fields.get(i), fields.get(1), fields.get(0), terminal.getBody(), terminal.beginLine, terminal.endLine);
			r.setJavaDocComment(findJavaDocComments(terminal));
		}
	}

	public static String findJavaDocComments(FSTTerminal terminal) {
		final String prefix = terminal.getSpecialTokenPrefix();
		final int start = prefix.indexOf("/**");
		final int end = prefix.lastIndexOf("*/");
		if ((start > -1) && (end > -1)) {
			return prefix.substring(start, end + "*/".length());
		}
		return null;
	}

	/**
	 *
	 * @param terminal body
	 * @return list(0) field modifiers<br> list(1) field type<br> ... field names
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
		body = body.trim();
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
	public void caseMethodDeclaration(FSTTerminal terminal) {
		// get name
		final String name = getMethodName(terminal);
		if (name == null) {
			return;
		}

		final String head = getHead(terminal.getBody(), name).replace("/*", "");
		final int index = head.trim().lastIndexOf(' ');

		// get return type
		final String returnType = head.substring(index + 1).trim();

		final String modifiers = (index == -1) ? "" : head.substring(0, index);
		String contractBody = "", contractCompKey = "";
		int startLine = -1;
		for (final FSTNode nonT1 : terminal.getParent().getChildren()) {
			if (nonT1.getType().equals("MethodSpecification")) {
				for (final FSTNode nonT2 : ((FSTNonTerminal) nonT1).getChildren()) {
					if (nonT2.getType().equals("Specification")) {
						for (final FSTNode nonT3 : ((FSTNonTerminal) nonT2).getChildren()) {
							if (nonT3.getType().equals("SpecCaseSeq")) {
								final FSTTerminal fstTerminal = (FSTTerminal) nonT3;
								startLine = fstTerminal.beginLine;
								contractBody = fstTerminal.getBody();
							}
							if (nonT3.getType().equals("ContractCompKey")) {
								contractCompKey = ((FSTTerminal) nonT3).getContractCompKey();
							}
						}
					}

				}
			}

		}
		// add method
		final IRoleElement r = addMethod(name, getMethodParameter(terminal), returnType, modifiers, terminal.getBody(), terminal.beginLine, terminal.endLine,
				false, contractBody, contractCompKey, startLine);
		r.setJavaDocComment(findJavaDocComments(terminal));
	}

	/**
	 * @param terminal
	 * @return contract string if existent
	 */
	/**
	 * @param body
	 * @return
	 */
	public String getHead(String body, String name) {
		// remove @annotations
		body = body.replaceAll("@\\w*\\W*", "");
		// remove spaces between name and ()
		body = body.replaceAll(name + "\\W*\\(", name + "(");
		return body.substring(0, body.indexOf(name + "("));
	}

	@Override
	public void caseConstructorDeclaration(FSTTerminal terminal) {
		// get name
		final String name = getMethodName(terminal);
		if (name == null) {
			return;
		}

		// get modifiers
		String modifiers = "";
		if (terminal.getBody().indexOf(name) >= 1) {
			modifiers = terminal.getBody().substring(0, terminal.getBody().indexOf(name) - 1);
		}

		String contractBody = "", contractCompKey = "";
		int startLine = -1;
		for (final FSTNode nonT1 : terminal.getParent().getChildren()) {
			if (nonT1.getType().equals("MethodSpecification")) {
				for (final FSTNode nonT2 : ((FSTNonTerminal) nonT1).getChildren()) {
					if (nonT2.getType().equals("Specification")) {
						for (final FSTNode nonT3 : ((FSTNonTerminal) nonT2).getChildren()) {
							if (nonT3.getType().equals("SpecCaseSeq")) {
								final FSTTerminal fstTerminal = (FSTTerminal) nonT3;
								startLine = fstTerminal.beginLine;
								contractBody = fstTerminal.getBody();
							}
							if (nonT3.getType().equals("ContractCompKey")) {
								contractCompKey = ((FSTTerminal) nonT3).getContractCompKey();
							}

						}
					}

				}
			}
		}

		// add constructor
		final IRoleElement r = addMethod(name, getMethodParameter(terminal), "void", modifiers, terminal.getBody(), terminal.beginLine, terminal.endLine, true,
				contractBody, contractCompKey, startLine);
		r.setJavaDocComment(findJavaDocComments(terminal));
	}

	private String getMethodName(FSTTerminal terminal) {
		if (terminal.getName().indexOf('(') != -1) {
			return terminal.getName().substring(0, terminal.getName().indexOf('('));
		}
		return null;
	}

	private LinkedList<String> getMethodParameter(FSTTerminal terminal) {
		final String parameter = terminal.getName().substring(terminal.getName().indexOf('(') + 1, terminal.getName().indexOf(')'));
		final LinkedList<String> parameterTypes = new LinkedList<String>();
		if (!"".equals(parameter) && !parameter.startsWith("{")) {
			final String[] p = parameter.split("[-]");
			for (int i = 0; i < p.length; i += 2) {
				parameterTypes.add(p[i]);
			}
		}
		return parameterTypes;
	}

	/**
	 * @param terminal
	 */
	@Override
	public void caseClassDeclarationType(FSTTerminal terminal) {
		if (modelBuilder.hasCurrentClassFragment()) {
			final String body = terminal.getBody().replaceAll("\\W", "");
			final FSTClassFragment currentClassFragment = modelBuilder.getCurrentClassFragment();
			currentClassFragment.setType(body);
			currentClassFragment.setLine(terminal.beginLine);
		}
	}

	@Override
	public void casePackage(FSTTerminal terminal) {
		if (modelBuilder.hasCurrentClassFragment()) {
			modelBuilder.getCurrentClassFragment().setPackage(terminal.getBody().replace("package ", "").replace(";", ""));
		}
	}

	@Override
	public void caseAddImport(FSTTerminal terminal) {
		if (modelBuilder.hasCurrentClassFragment()) {
			modelBuilder.getCurrentClassFragment().addImport(terminal.getBody());
		}
	}

	@Override
	public void caseImplementsList(FSTTerminal terminal) {
		if (modelBuilder.hasCurrentClassFragment()) {
			final String body = terminal.getBody().replace("implements ", "");
			final String[] classNames = body.split(", ");
			for (final String className : classNames) {
				modelBuilder.getCurrentClassFragment().addImplement(className);
			}
		}
	}

	@Override
	public void caseExtendsList(FSTTerminal terminal) {
		if (modelBuilder.hasCurrentClassFragment()) {
			final String body = terminal.getBody().replace("extends ", "");
			final String[] classNames = body.split(", ");
			for (final String className : classNames) {
				modelBuilder.getCurrentClassFragment().addExtend(className);
			}
		}
	}

	@Override
	public void caseInvariant(FSTTerminal terminal) {
		final FSTInvariant invariant = new FSTInvariant(terminal.getName(), terminal.getBody(), terminal.beginLine, terminal.endLine);
		if (!modelBuilder.getCurrentClassFragment().add(invariant)) {
			FeatureHouseCorePlugin.getDefault().logError("Invariant " + invariant.getBody() + "was not added to FSTModel.", null);
		}
	}

	@Override
	public void caseJMLSpecCaseSeq(FSTTerminal terminal) {}

	@Override
	public void caseModifiers(FSTTerminal terminal) {
		if (modelBuilder.hasCurrentClassFragment()) {
			final String body = terminal.getBody().replaceAll("\\W", "");
			modelBuilder.getCurrentClassFragment().setModifiers(body);
		}
	}
}
