/**
 * 
 */
package org.deltaj.generator;

import java.util.List;

import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.Product;
import org.deltaj.util.DeltaJUtils;
import org.deltaj.util.DeltasToApply;

import com.google.inject.Inject;

/**
 * Given a Product, finds all the deltas to apply.
 * 
 * @author bettini
 * 
 */
public class DeltasToApplyFinder {

	@Inject
	protected PropositionalFormulaChecker formulaChecker = new PropositionalFormulaChecker();

	public DeltasToApply getDeltas(Product product) {
		DeltasToApply deltas = new DeltasToApply();
		List<ModuleReference> deltaModules = DeltaJUtils.getDeltaModules(product);
		List<Feature> features = product.getFeatures();

		for (ModuleReference deltaModule : deltaModules) {
			if (formulaChecker.check(deltaModule.getWhen(), features))
				deltas.add(deltaModule.getDeltaModule());
		}

		return deltas;
	}
}
