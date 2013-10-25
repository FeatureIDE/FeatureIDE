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
import de.ovgu.featureide.fm.core.editing.NodeCreator;

public class ContextFilter2 implements ISignatureFilter {
	private final InterfaceProject interfaceProject;
	private final HashMap<int[], Boolean> satMap;
	private final Node[] fixClauses;
	
	public ContextFilter2(String featurename, InterfaceProject interfaceProject) {
		this(IOConstants.buildNodeForFeature(featurename), interfaceProject);
	}
	
	public ContextFilter2(Node[] constraints, InterfaceProject interfaceProject) {
		this.interfaceProject = interfaceProject;
		satMap = new HashMap<int[], Boolean>();
		
		fixClauses = new Node[constraints.length + 1];
		fixClauses[0] = NodeCreator.createNodes(interfaceProject.getFeatureModel());
		System.arraycopy(constraints, 0, fixClauses, 1, constraints.length);	
	}

	@Override
	public boolean isValid(AbstractSignature signature) {	
		int[] features = signature.getFeatureIDs();
		Boolean sat = satMap.get(features);
		if (sat == null) {
			Node[] clauses = new Node[features.length + fixClauses.length];
			int j = 0;
			for (int featureID : features) {
				clauses[j++] = new Literal(interfaceProject.getFeatureName(featureID), false);
			}
			System.arraycopy(fixClauses, 0, clauses, j, fixClauses.length);
			
			SatSolver solver = new SatSolver(new And(clauses), 2006);
			try {
				sat = !solver.isSatisfiable();						
				satMap.put(features, sat);
			} catch (TimeoutException e) {
				MPLPlugin.getDefault().logError(e);
			}
		}
		return sat != null && sat;
	}

}
