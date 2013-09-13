package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;

/**
 * Convenience-class to evaluate constraints which is just extracting their
 * names.
 * 
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public class ConstraintNode extends LazyParent {
	protected Constraint constr;
	
	public ConstraintNode(Constraint constr) {
		super("Constraint", constr.toString());
		this.constr = constr;
		lazy = false;
	}

	@Override
	protected void initChildren() {
		
	}
}