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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.ovgu.featureide.core.signature.base.AbstractSignature;

/**
 * TODO description
 * 
 * @author steffen
 */
public class RefactoringSignature {
	private AbstractSignature declaration;
	
	private AbstractSignature invocationDeclaration;
	
	private Map<AbstractSignature, Set<AbstractSignature>> invocations = new HashMap<>();
	
	private final String absolutePath;
	
	public RefactoringSignature(final String absolutePath, final AbstractSignature declaration) {
		this.absolutePath = absolutePath;
		this.declaration = declaration;
	}
	
	public String getAbsolutePathToFile() {
		return absolutePath;
	}
	
	public AbstractSignature getDeclaration() {
		return declaration;
	}
	
	public void setDeclaration(AbstractSignature declaration) {
		this.declaration = declaration;
	}

	public Map<AbstractSignature, Set<AbstractSignature>> getInvocations() {
		return invocations;
	}

	public void addInvocation(final AbstractSignature invocation, final AbstractSignature invokedSignature) {
		
		Set<AbstractSignature> invokedSignatures;
		if (this.invocations.containsKey(invocation)) {
			invokedSignatures = invocations.get(invocation);
		}
		else {
			invokedSignatures = new HashSet<>();
			this.invocations.put(invocation, invokedSignatures);
		}
		
		invokedSignatures.add(invokedSignature);
	}
	
	@Override
	public String toString() {
		return "File: " + absolutePath + "; declaration: " + declaration + "; invocations: " + invocations;
	}

}
