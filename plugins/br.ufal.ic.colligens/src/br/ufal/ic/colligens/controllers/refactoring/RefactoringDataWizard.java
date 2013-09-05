package br.ufal.ic.colligens.controllers.refactoring;

import org.eclipse.ltk.ui.refactoring.RefactoringWizard;

public class RefactoringDataWizard extends RefactoringWizard {

	public RefactoringDataWizard(RefactoringController refactoring,
			String pageTitle) {
		super(refactoring, 
				 PREVIEW_EXPAND_FIRST_NODE);
		setDefaultPageTitle(pageTitle);
		setForcePreviousAndNextButtons(true);
	}

	@Override
	protected void addUserInputPages() {
//		addPage(new RefactoringDataInputPage("IntroduceIndirectionInputPage"));
	}

}
