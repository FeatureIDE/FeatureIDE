
package org.deltaj.ui.quickfix;

import org.deltaj.deltaj.Configuration;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.deltaj.ClassRemoval;
import org.deltaj.transformations.actions.DeltaJActionFactory;
import org.deltaj.transformations.formula.DeltaJFormulaOptimizer;
import org.deltaj.transformations.resolve.DeltaJRemovalActionResolver;
import org.deltaj.validation.ValidationCode;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.xtext.ui.editor.model.edit.IModificationContext;
import org.eclipse.xtext.ui.editor.model.edit.ISemanticModification;
import org.eclipse.xtext.ui.editor.quickfix.DefaultQuickfixProvider;
import org.eclipse.xtext.ui.editor.quickfix.Fix;
import org.eclipse.xtext.ui.editor.quickfix.IssueResolutionAcceptor;
import org.eclipse.xtext.validation.Issue;

public class DeltaJQuickfixProvider extends DefaultQuickfixProvider {

	@Fix(ValidationCode.REMOVES_CLASS)
	public void makeRemovesClassMonotonic(Issue issue, IssueResolutionAcceptor acceptor) {
		acceptor.accept(issue, "Make Monotonic", "Refactor this removes statement.", null, new ISemanticModification() {
			
			@Override
			public void apply(EObject element, IModificationContext context)
					throws Exception {
				
				ClassRemoval removesClass = (ClassRemoval) element;
				
				new DeltaJRemovalActionResolver(DeltaJActionFactory.get(removesClass)).resolve();
			}
		});
	}

	@Fix(ValidationCode.OPTIMIZE_WHEN)
	public void optimizeWhenFormula(Issue issue, IssueResolutionAcceptor acceptor) {
		acceptor.accept(issue, "Optimize When Formula", "Convert the when-formula into an optimized form.", null, new ISemanticModification() {
			
			@Override
			public void apply(EObject element, IModificationContext context)
					throws Exception {
				
				ModuleReference moduleReference = (ModuleReference) element;
				
				PropositionalFormula optimizedFormula = new DeltaJFormulaOptimizer(moduleReference.getWhen()).optimize();
				
				moduleReference.setWhen(optimizedFormula);
			}
		});
	}

	@Fix(ValidationCode.OPTIMIZE_CONFIGURATION)
	public void optimizeConfigurationFormula(Issue issue, IssueResolutionAcceptor acceptor) {
		acceptor.accept(issue, "Optimize Configuration Formula", "Convert the configuration-formula into an optimized form.", null, new ISemanticModification() {
			
			@Override
			public void apply(EObject element, IModificationContext context)
					throws Exception {
				
				Configuration configuration = (Configuration) element;
				
				PropositionalFormula optimizedFormula = new DeltaJFormulaOptimizer(configuration.getFormula()).optimize();
				
				configuration.setFormula(optimizedFormula);
			}
		});
	}
}
