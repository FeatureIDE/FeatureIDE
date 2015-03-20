package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import java.util.LinkedList;

import de.ovgu.featureide.core.fstmodel.FSTInvariant;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes.AbstractSortModeNode;

/**
 * TODO description
 * 
 * @author Schleicher Miro
 */
public class MethodContractNodeParent extends AbstractSortModeNode {

	FSTMethod fstMethod;

	public MethodContractNodeParent(String discription, FSTMethod nameMethod, LinkedList<FSTMethod> allMethodsList) {
		super(discription);
		fstMethod = nameMethod;
		int numberOfMethods = countMethodsWithSameName(allMethodsList);
		super.setValue(numberOfMethods);

	}
	
	private int countMethodsWithSameName(LinkedList<FSTMethod> methods) {
		int c = 0;
		for (FSTMethod tempMethod : methods) {
			if (tempMethod.getFullIdentifier().equals(fstMethod.getFullIdentifier())) {
				c++;
				addChild(new MethodSubNodeParent(tempMethod.getRole().getFeature().getName(), tempMethod));
			}
		}
		return c;

	}

	@Override
	protected void initChildren() {
		// TODO Auto-generated method stub
		
	}

}
