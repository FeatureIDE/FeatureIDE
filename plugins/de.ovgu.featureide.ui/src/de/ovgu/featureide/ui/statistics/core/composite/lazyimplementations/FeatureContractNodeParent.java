package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import java.util.LinkedList;

import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes.AbstractSortModeNode;

/**
 * TODO description
 * 
 * @author Schleicher Miro
 */
public class FeatureContractNodeParent extends AbstractSortModeNode {

	FSTMethod fstMethod;

	public FeatureContractNodeParent(String description, FSTMethod method, LinkedList<FSTMethod> allContractsFeature) {
		super(description);
		fstMethod = method;
		int numberOfContractsInFeature = countFeature(allContractsFeature);
		super.setValue(numberOfContractsInFeature);	
	}

	@Override
	protected void initChildren() {
		// TODO Auto-generated method stub

	}

	public int countFeature(LinkedList<FSTMethod> methods) {
		
		int c = 0;
		for (FSTMethod tempMethod : methods) {
			if (tempMethod.getRole().getFeature().equals(fstMethod.getRole().getFeature())) {
				c++;

				addChild(new MethodSubNodeParent(tempMethod.getFullIdentifier(), tempMethod));
			}
		}
		return c;
		
	}
	
}
