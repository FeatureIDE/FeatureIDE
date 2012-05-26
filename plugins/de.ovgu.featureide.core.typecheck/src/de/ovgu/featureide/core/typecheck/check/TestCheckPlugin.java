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
package de.ovgu.featureide.core.typecheck.check;

import AST.ASTNode;
import AST.FieldDeclaration;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.typecheck.parser.ClassTable;
import de.ovgu.featureide.core.typecheck.parser.ClassTableEntry;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * TODO description
 * 
 * @author soenke
 */
public class TestCheckPlugin extends AbstractCheckPlugin {

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.core.typecheck.check.ICheckPlugin#invokeCheck(de.ovgu
	 * .featureide.core.IFeatureProject,
	 * de.ovgu.featureide.core.typecheck.parser.ClassTable)
	 */
	@Override
	public void invokeCheck(FeatureModel fm) {

	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.core.typecheck.check.ICheckPlugin#invokeNodeParse(
	 * AST.ASTNode)
	 */
	@Override
	public void invokeNodeParse(Feature feature, ASTNode node) {
		// TODO Auto-generated method stub

	}
}
