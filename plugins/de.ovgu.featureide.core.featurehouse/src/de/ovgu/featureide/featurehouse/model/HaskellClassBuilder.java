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
import de.ovgu.featureide.core.fstmodel.FSTModel;

/**
 * Builds Classes for the {@link FSTModel} for <code>FeatureHouse</code> Haskel files.
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
		FSTField field = new FSTField(terminal.getBody(), "", 0, "", terminal.getBody(), terminal.beginLine, terminal.endLine);
		field.setOwn(modelBuilder.getCurrentFile());
		modelBuilder.getCurrentClass().add(field);
	}
	
	@Override
	void caseMethodDeclaration(FSTTerminal terminal) {
		if (!terminal.getBody().contains("::")) {
			return;
		}
		LinkedList<String> method = getMethod(terminal.getBody());
		if (method == null) {
			return;
		}
		LinkedList<String> parameter = new LinkedList<String>();
		parameter.add(method.get(1));
		addMethod(method.get(0), parameter, "void", "", terminal.getBody(), terminal.beginLine, terminal.endLine, false);
	}
	
	/**
	 * 
	 * @param terminal body
	 * @return list(0) method name
	 * 		   list(1) method type
	 */
	public LinkedList<String> getMethod(String body) {
		LinkedList<String> method = new LinkedList<String>();
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
