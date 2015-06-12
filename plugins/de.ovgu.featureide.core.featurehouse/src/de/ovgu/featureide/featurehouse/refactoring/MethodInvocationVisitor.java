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
import java.util.List;

import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.MethodInvocation;

import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;

/**
 * TODO description
 * 
 * @author steffen
 */
public class MethodInvocationVisitor extends AbstractASTVisitor<FujiMethodSignature> {

	  public MethodInvocationVisitor(final FujiMethodSignature signature)
	  {
		  super(signature);
	  }
	
	@Override
	public boolean visit(MethodInvocation node) {
		
		 if (hasSameName(node.getName().getFullyQualifiedName()) && hasSameParameters(node)) 
		 {
			visitedNodes.add(node);
		 }
		 return false;
	}
	
	  
	  private boolean hasSameParameters(MethodInvocation node)
	  {
		 return getNodeParameters(node).equals(signature.getParameterTypes());
	  }

	  private List<String> getNodeParameters(MethodInvocation node)
	  {
		  List<String> parameters = new ArrayList<String>();
			IMethodBinding methodBinding = node.resolveMethodBinding();
			for (ITypeBinding type : methodBinding.getParameterTypes()) {
				
				parameters.add(type.getErasure().getName());
			}
        return parameters;
	  }

}
