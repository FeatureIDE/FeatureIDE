package de.ovgu.featureide.featurehouse.ui.handlers;
import org.eclipse.ltk.ui.refactoring.RefactoringWizardOpenOperation;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.featurehouse.refactoring.RenameFieldRefactoring;
import de.ovgu.featureide.featurehouse.refactoring.RenameLocalVariableRefactoring;
import de.ovgu.featureide.featurehouse.refactoring.RenameMethodRefactoring;
import de.ovgu.featureide.featurehouse.refactoring.RenameRefactoring;
import de.ovgu.featureide.featurehouse.refactoring.RenameRefactoringWizard;
import de.ovgu.featureide.featurehouse.refactoring.RenameTypeRefactoring;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiClassSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiFieldSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiLocalVariableSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;


public class RenameHandler extends RefactoringHandler {

	@Override
	protected void singleAction(Object element, String file) 
	{
		try {
			IFeatureProject featureProject = getFeatureProject();
			if (featureProject == null)
				return;

			RenameRefactoring refactoring;
			if (element instanceof FujiMethodSignature){
				FujiMethodSignature method = (FujiMethodSignature) element;

				if (method.isConstructor())
					refactoring = new RenameTypeRefactoring((FujiClassSignature)method.getParent(), featureProject);
				else
					refactoring = new RenameMethodRefactoring(method, featureProject);
			} else if (element instanceof FujiClassSignature){
				refactoring = new RenameTypeRefactoring((FujiClassSignature) element, featureProject);
			} else if (element instanceof FujiFieldSignature){
				refactoring = new RenameFieldRefactoring((FujiFieldSignature) element, featureProject);
			} else if (element instanceof FujiLocalVariableSignature){
				refactoring = new RenameLocalVariableRefactoring((FujiLocalVariableSignature) element, featureProject);
			} else
				return;

			RenameRefactoringWizard refactoringWizard = new RenameRefactoringWizard(refactoring);
			RefactoringWizardOpenOperation op = new RefactoringWizardOpenOperation(refactoringWizard);
			op.run(getShell(), "Rename-Refactoring");
		} catch (InterruptedException e) {
		}
	}
}
