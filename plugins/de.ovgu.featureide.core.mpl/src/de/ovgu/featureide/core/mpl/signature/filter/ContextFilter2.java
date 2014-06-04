/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
* See http://www.fosd.de/featureide/ for further information.
*/
package de.ovgu.featureide.core.mpl.signature.filter;

import java.util.HashMap;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.core.mpl.InterfaceProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.io.IOConstants;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractSignature.FeatureData;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

public class ContextFilter2 implements ISignatureFilter {
	private final InterfaceProject interfaceProject;
	private final HashMap<FeatureData[], Boolean> satMap;
	private final Node[] fixClauses;
	
	public ContextFilter2(String featurename, InterfaceProject interfaceProject) {
		this(IOConstants.buildNodeForFeature(featurename), interfaceProject);
	}
	
	public ContextFilter2(Node[] constraints, InterfaceProject interfaceProject) {
		this.interfaceProject = interfaceProject;
		satMap = new HashMap<FeatureData[], Boolean>();
		
		fixClauses = new Node[constraints.length + 1];
		fixClauses[0] = NodeCreator.createNodes(interfaceProject.getFeatureModel());
		System.arraycopy(constraints, 0, fixClauses, 1, constraints.length);	
	}

	@Override
	public boolean isValid(AbstractSignature signature) {	
		FeatureData[] featureDataArray = signature.getFeatureData();
//		int[] features = signature.getFeatureIDs();
		Boolean sat = satMap.get(featureDataArray);
		if (sat == null) {
			Node[] clauses = new Node[featureDataArray.length + fixClauses.length];
			int j = 0;
			for (FeatureData featureData : featureDataArray) {
				clauses[j++] = new Literal(interfaceProject.getFeatureName(featureData.getId()), false);
			}
			System.arraycopy(fixClauses, 0, clauses, j, fixClauses.length);
			
			SatSolver solver = new SatSolver(new And(clauses), 2006);
			try {
				sat = !solver.isSatisfiable();						
				satMap.put(featureDataArray, sat);
			} catch (TimeoutException e) {
				MPLPlugin.getDefault().logError(e);
			}
		}
		return sat != null && sat;
	}

}
