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

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.base.AFeatureData;
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.FOPFeatureData;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiFieldSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiLocalVariableSignature;

/**
 * TODO description
 * 
 * @author steffen
 */
public class LocalVariableSignatureMatcher extends SignatureMatcher {

	public LocalVariableSignatureMatcher(ProjectSignatures signatures, AbstractSignature selectedElement, String newName) {
		super(signatures, selectedElement, newName);
	}

	@Override
	protected boolean hasSameType(AbstractSignature signature) {
		return (signature instanceof FujiFieldSignature);
	}
	
	@Override
	protected Set<AbstractSignature> determineMatchedSignatures() {

		final Set<AbstractSignature> result = new HashSet<>();

		FujiLocalVariableSignature localSig = (FujiLocalVariableSignature) selectedElement;

		final AbstractMethodSignature declaringMethod = localSig.getDeclaringMethod();
		if (declaringMethod.isConstructor()) {

			final AbstractMethodSignature realDeclaringMethod = getRealDeclaringMethod(localSig, declaringMethod);
			final AFeatureData firstFeatureData = localSig.getFirstFeatureData();
			final FOPFeatureData newFopData = new FOPFeatureData(firstFeatureData.getID(), 0, 0);
			newFopData.setConstraint(firstFeatureData.getConstraint());
			newFopData.setAbsoluteFilePath(firstFeatureData.getAbsoluteFilePath());
			newFopData.addInvokedSignature(realDeclaringMethod);

			localSig.setFeatureData(new FOPFeatureData[]{newFopData});
		}
		result.add(localSig);

		return result;
	}

	private AbstractMethodSignature getRealDeclaringMethod(FujiLocalVariableSignature localSig, final AbstractMethodSignature declaringMethod) {
		final String parentName = localSig.getParent().getFullName();
		if (classes.containsKey(parentName)){
			Iterator<AbstractMethodSignature> iterator = classes.get(parentName).getMethods().iterator();
			while(iterator.hasNext()){
				AbstractMethodSignature next = iterator.next();
				if (next.equals(declaringMethod)) 
					return next;
			}
		}
		return null;
	}
		
		

}
