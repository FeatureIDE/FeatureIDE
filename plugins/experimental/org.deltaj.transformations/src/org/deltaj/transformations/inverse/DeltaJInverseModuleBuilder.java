package org.deltaj.transformations.inverse;

import java.util.Set;
import org.deltaj.deltaj.DeltaAction;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.DeltajFactory;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.Product;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.deltaj.Program;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.transformations.exceptions.DeltaJModuleNotUsedByProductException;
import org.deltaj.transformations.exceptions.DeltaJModuleNotUsedBySplException;
import org.deltaj.transformations.finder.DeltaJModuleFinder;
import org.deltaj.transformations.finder.DeltaJModuleReferenceFinder;
import org.deltaj.transformations.finder.product.DeltaJProductByNameFinder;
import org.deltaj.transformations.formula.DeltaJFormulaEvaluator;
import org.deltaj.transformations.modules.references.DeltaJModuleReference;
import org.deltaj.transformations.utils.GrammarUtils;

/**
 * This class build the inverse of a given delta module.
 * 
 * @author Oliver Richers
 */
public class DeltaJInverseModuleBuilder {

	private static final String INVERSE_NAME_FORMAT = "%s_inverse";
	private final DeltajFactory factory;
	private final Product product;
	private final ProductLine splSpecification;
	private final Set<Feature> enabledFeatures;
	private final DeltaModule deltaModule;
	private final DeltaJModuleReference moduleReference;

	public DeltaJInverseModuleBuilder(Program program, String productName, String moduleName) {

		this(new DeltaJProductByNameFinder(program, productName).findOrThrow(), moduleName);
	}

	public DeltaJInverseModuleBuilder(Product product, String moduleName) {

		this(product, new DeltaJModuleFinder(GrammarUtils.getProgram(product), moduleName).findOrThrow());
	}

	public DeltaJInverseModuleBuilder(Product product, DeltaModule deltaModule) {

		this.factory = DeltajFactory.eINSTANCE;
		this.product = product;
		this.splSpecification = product.getProductLine();
		this.enabledFeatures = GrammarUtils.getFeatures(product);
		this.deltaModule = deltaModule;
		this.moduleReference = findModuleReferenceContext();
	}

	private DeltaJModuleReference findModuleReferenceContext() {

		for (DeltaJModuleReference moduleReference: new DeltaJModuleReferenceFinder(deltaModule).findMap().values()) {
			if (moduleReference.getSplSpecification() == splSpecification) {
				return moduleReference;
			}
		}

		return null;
	}

	public DeltaModule build() {

		verifyValidityOfOperation();

		DeltaModule inverseModule = factory.createDeltaModule();

		inverseModule.setName(String.format(INVERSE_NAME_FORMAT, deltaModule.getName()));

		InverseActionBuilderDispatcher builderDispatcher = new InverseActionBuilderDispatcher(factory);

		for (DeltaAction deltaAction: deltaModule.getDeltaActions()) {
			DeltaAction inverseAction = builderDispatcher.dispatch(deltaAction);
			inverseModule.getDeltaActions().add(inverseAction);
		}

		return inverseModule;
	}

	private void verifyValidityOfOperation() {

		verifyModuleIsUsedBySpl();
		verifyModuleIsUsedByProduct();
	}

	private void verifyModuleIsUsedBySpl() {

		if (moduleReference == null) {
			throw new DeltaJModuleNotUsedBySplException(splSpecification, deltaModule);
		}
	}

	private void verifyModuleIsUsedByProduct() {

		PropositionalFormula formula = moduleReference.getStatement().getWhen();

		boolean used = new DeltaJFormulaEvaluator(formula).evaluate(enabledFeatures);

		if (!used) {
			throw new DeltaJModuleNotUsedByProductException(product, deltaModule);
		}
	}
}
