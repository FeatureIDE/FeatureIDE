/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.featurehouse.refactoring;

import java.util.HashSet;
import java.util.Set;

import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.SignaturePosition;

/**
 * TODO description
 * 
 * @author steffen
 */
public class RefactoringSignature {

	private AbstractSignature declaration;

	private final String absolutePath;

	private final Set<SignaturePosition> positions;

	public RefactoringSignature(final String absolutePath, final AbstractSignature declaration) {
		this.absolutePath = absolutePath;
		this.declaration = declaration;
		this.positions = new HashSet<>();
	}

	public String getAbsolutePathToFile() {
		return absolutePath;
	}

	public AbstractSignature getDeclaration() {
		return declaration;
	}

	public void addPosition(final SignaturePosition position) {
		positions.add(position);
	}

	public Set<SignaturePosition> getPositions() {
		return positions;
	}

	@Override
	public String toString() {
		return "File: " + absolutePath + "; declaration: " + declaration;
	}

}
