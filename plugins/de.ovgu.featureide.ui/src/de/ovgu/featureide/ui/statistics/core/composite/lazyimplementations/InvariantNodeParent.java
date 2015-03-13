
package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import java.util.LinkedList;

import de.ovgu.featureide.core.fstmodel.FSTInvariant;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * TODO description
 * 
 * @author Schleicher Miro
 */
public class InvariantNodeParent extends Parent {
	
	FSTInvariant fstInvariant;
	
	public InvariantNodeParent(String discription, FSTInvariant fstInvariant, LinkedList<FSTInvariant> allInvariants) {
		super(discription);
		this.fstInvariant = fstInvariant;
		int numberOfInvariants = countInvariantsWithSameName(allInvariants);
		setValue(new Integer(numberOfInvariants));
	}
	
	
	private int countInvariantsWithSameName(LinkedList<FSTInvariant> invariants) {
		int c = 0;
		for (FSTInvariant tempInvariant : invariants) {
			if (tempInvariant.getRole().getClassFragment().getFullIdentifier().equals(fstInvariant.getRole().getClassFragment().getFullIdentifier())) {
				c++;

				addChild(new Parent(tempInvariant.getRole().getFeature().getName(), tempInvariant));
			}
		}
		return c;
	}
	
	public FSTInvariant getInvariant() {
		return fstInvariant;
	}
}
