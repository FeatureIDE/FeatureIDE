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
 * 
 * @author Jens Meinicke
 */
public class HaskellClassBuilder extends ClassBuilder {

	public HaskellClassBuilder(FeatureHouseModelBuilder modelBuilder) {
		super(modelBuilder);
	}
	
	@Override
	void caseFieldDeclaration(FSTTerminal terminal) {
		FSTField field = new FSTField(terminal.getBody(), "", 0, "");
		field.setOwn(modelBuilder.getCurrentFile());
		modelBuilder.getCurrentClass().fields.put(field.getIdentifier(), field);
	}
	
	@Override
	void caseMethodDeclaration(FSTTerminal terminal) {
		if (!terminal.getBody().contains("::")) {
			return;
		}
		String name = terminal.getBody().substring(0, terminal.getBody().indexOf("::")); 
		while (name.endsWith(" ")) {
			name = name.substring(0, name.length() - 1);
		}
		if (name.contains(" ")) {
			return;
		}
		LinkedList<String> parameterTypes = new LinkedList<String>();
		String parameter = terminal.getBody().substring(terminal.getBody().indexOf("::") + 2);
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
		parameterTypes.add(parameter);
		addMethod(name, parameterTypes, "void", "");
	}

	private void addMethod(String name, LinkedList<String> parameterTypes, 
			String returnType, String modifiers) {
		FSTMethod method = new FSTMethod(name, parameterTypes, returnType, modifiers);								
		method.setOwn(modelBuilder.getCurrentFile());
		modelBuilder.getCurrentClass().methods.put(method.getIdentifier(), method);
	}
}
