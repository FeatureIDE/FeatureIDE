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

import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclaration;

import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;


/**
 * TODO description
 * 
 * @author steffen
 */
public class MethodDeclarationVisitor extends AbstractASTVisitor<FujiMethodSignature> {

	public MethodDeclarationVisitor(final FujiMethodSignature signature) {
		super(signature);
	}

	  @Override
	  public boolean visit(MethodDeclaration node) {
		  
		 if (hasSameName(node.getName().getFullyQualifiedName()) && hasSameParameters(node)) 
		 {
			 visitedNodes.add(node);
		 }
		 return false;
	  }
	
	  
	  private boolean hasSameParameters(MethodDeclaration node)
	  {
		 return getNodeParameters(node).equals(signature.getParameterTypes());
	  }

	  private List<String> getNodeParameters(MethodDeclaration node)
	  {
		  List<String> parameters = new ArrayList<String>();
        for (Object parameter : node.parameters()) {
            VariableDeclaration variableDeclaration = (VariableDeclaration) parameter;
            String type = variableDeclaration.getStructuralProperty(SingleVariableDeclaration.TYPE_PROPERTY)
                    .toString();
            for (int i = 0; i < variableDeclaration.getExtraDimensions(); i++) {
                type += "[]";
            }
            parameters.add(type);
        }
        return parameters;
	  }

}
