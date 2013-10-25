package de.ovgu.featureide.core.mpl.signature.filter;

import java.util.Arrays;

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

public class ContextFilter implements ISignatureFilter {
//	private class ka {
//		private final byte[] features;
//		
//		public ka() {
//			features = new byte[selcetedFeatures.length];
//			for (int i = 0; i < selcetedFeatures.length; i++) {
//				features[i] = (byte) (selcetedFeatures[i] ? 1 : -1);
//			}
//		}
//		
//		public void set(int id) {
//			features[id] = 0;
//		}
//
//		@Override
//		public boolean equals(Object obj) {
//			return Arrays.equals(features, ((ka) obj).features);
//		}
//
//		@Override
//		public int hashCode() {
//			return Arrays.hashCode(features);
//		}
//	}
	
//	private final HashMap<ka, Boolean> satMap = new HashMap<ka, Boolean>();
	
	private final InterfaceProject interfaceProject;
	private final Node fmNode;
	private final boolean[] selcetedFeatures;
	private SatSolver solver;
	
	public ContextFilter(String featurename, InterfaceProject interfaceProject) {
		this(IOConstants.buildNodeForFeature(featurename), interfaceProject);
	}
	
	public ContextFilter(Node[] constraints, InterfaceProject interfaceProject) {
		this.interfaceProject = interfaceProject;
		fmNode = NodeCreator.createNodes(interfaceProject.getFeatureModel());
		selcetedFeatures = new boolean[interfaceProject.getFeatureModel().getNumberOfFeatures()];
		
		init(constraints);
	}
	
	public void init(Node[] constraints) {
		Node[] fixClauses = new Node[constraints.length + 1];
		fixClauses[0] = fmNode;
		System.arraycopy(constraints, 0, fixClauses, 1, constraints.length);
		Arrays.fill(selcetedFeatures, false);
		
		solver = new SatSolver(new And(fixClauses), 2000);
		
		for (Literal literal : solver.knownValues()) {
			int id = interfaceProject.getFeatureID(literal.var.toString());
			if (id > -1) {
				selcetedFeatures[id] = true;
			}
		}
	}
	
	public void init(String featurename) {
		init(IOConstants.buildNodeForFeature(featurename));
	}

	@Override
	public boolean isValid(AbstractSignature signature) {
		int[] ids = signature.getFeatureIDs();
		Node[] cxy = new Node[ids.length];
//		ka a = new ka();
		for (int i = 0; i < ids.length; ++i) {
			int id = ids[i];
			if (selcetedFeatures[id]) {
				return true;
			} 
			cxy[i] = new Literal(interfaceProject.getFeatureName(id), false);
//			a.set(id);
		}
		try {
//			Boolean sat = satMap.get(a);
//			if (sat == null)  {
//				sat = !solver.isSatisfiable(cxy);
//				satMap.put(a, sat);
//			}
//			return sat;
			return !solver.isSatisfiable(cxy);
		} catch (TimeoutException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}
	}

}
