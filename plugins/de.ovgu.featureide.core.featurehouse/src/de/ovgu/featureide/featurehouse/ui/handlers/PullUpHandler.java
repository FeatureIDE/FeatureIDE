package de.ovgu.featureide.featurehouse.ui.handlers;
import org.eclipse.ltk.ui.refactoring.RefactoringWizardOpenOperation;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.featurehouse.refactoring.pullUp.PullUpMethodRefactoring;
import de.ovgu.featureide.featurehouse.refactoring.pullUp.PullUpRefactoring;
import de.ovgu.featureide.featurehouse.refactoring.pullUp.PullUpRefactoringWizard;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiLocalVariableSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;


public class PullUpHandler extends RefactoringHandler {

	protected void singleAction(Object element, String file) 
	{
		try {
			IFeatureProject featureProject = getFeatureProject();
			if (featureProject == null)
				return;

			if (element instanceof FujiLocalVariableSignature)
				return;
			
			PullUpRefactoring pulUp = new PullUpMethodRefactoring((FujiMethodSignature) element, featureProject, file); 
			PullUpRefactoringWizard refactoringWizard = new PullUpRefactoringWizard(pulUp);
			RefactoringWizardOpenOperation op = new RefactoringWizardOpenOperation(refactoringWizard);
			op.run(getShell(), "PullUp-Refactoring");
		} catch (InterruptedException e) {
		}
	}
}
