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
package de.ovgu.featureide.featurehouse.refactoring.matcher;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiClassSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;

/**
 * TODO description
 * 
 * @author steffen
 */
public class TypeSignatureMatcher extends SignatureMatcher {

	public TypeSignatureMatcher(ProjectSignatures signatures, AbstractSignature selectedElement, String newName) {
		super(signatures, selectedElement, newName);
	}

	@Override
	protected boolean hasSameType(AbstractSignature signature) {
		return (signature instanceof FujiClassSignature);
	}

	@Override
	protected Set<AbstractSignature> determineMatchedSignatures() {

		if (!hasSameType(selectedSignature)) return Collections.emptySet();

		final Set<AbstractSignature> result = new HashSet<>();
		result.add(selectedSignature);

		FujiMethodSignature constructor = getConstructor();
		if (constructor != null) result.add(constructor);

		return result;
	}

	private FujiMethodSignature getConstructor() {
		final SignatureIterator iter = signatures.iterator();
		while (iter.hasNext()) {
			final AbstractSignature signature = iter.next();

			if (!(signature instanceof FujiMethodSignature)) continue;
			final FujiMethodSignature methodSignature = (FujiMethodSignature) signature;

			if (methodSignature.isConstructor() && methodSignature.getFullName().equals(selectedSignature.getFullName() + "." + selectedSignature.getName())) {
				return methodSignature;
			}
		}
		return null;
	}

}
