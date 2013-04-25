/**
 * 
 */
package org.deltaj.generator;

import java.util.List;

import org.deltaj.deltaj.And;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.FeatureRef;
import org.deltaj.deltaj.Negation;
import org.deltaj.deltaj.Or;
import org.deltaj.deltaj.PropFalse;
import org.deltaj.deltaj.PropParen;
import org.deltaj.deltaj.PropTrue;
import org.deltaj.deltaj.PropositionalFormula;
import org.eclipse.xtext.util.PolymorphicDispatcher;

/**
 * Checks whether a formula is verified, given a list of features.
 * 
 * @author bettini
 * 
 */
public class PropositionalFormulaChecker {

	private PolymorphicDispatcher<Boolean> dispatcher = PolymorphicDispatcher
			.createForSingleTarget("checkCase", 2, 2, this);

	public boolean check(PropositionalFormula when, List<Feature> features) {
		if (when == null)
			return true;
		if (features == null || features.size() == 0)
			return false;
		return dispatcher.invoke(when, features);
	}

	protected boolean checkCase(FeatureRef feature, List<Feature> features) {
		return feature.getFeature() != null
				&& features.contains(feature.getFeature());
	}

	protected boolean checkCase(Negation negation, List<Feature> features) {
		return !check(negation.getFormula(), features);
	}

	protected boolean checkCase(PropParen paren, List<Feature> features) {
		return check(paren.getFormula(), features);
	}

	protected boolean checkCase(PropTrue propTrue, List<Feature> features) {
		return true;
	}

	protected boolean checkCase(PropFalse propFalse, List<Feature> features) {
		return false;
	}
	
	protected boolean checkCase(And and, List<Feature> features) {
		return check(and.getLeft(), features)
				&& check(and.getRight(), features);
	}

	protected boolean checkCase(Or or, List<Feature> features) {
		return check(or.getLeft(), features) || check(or.getRight(), features);
	}

}
