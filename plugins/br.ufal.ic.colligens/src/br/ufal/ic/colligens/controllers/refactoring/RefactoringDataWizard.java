package br.ufal.ic.colligens.controllers.refactoring;

import org.eclipse.ltk.ui.refactoring.RefactoringWizard;

public class RefactoringDataWizard extends RefactoringWizard {

	public RefactoringDataWizard(RefactoringController refactoring,
			String pageTitle) {
		super(refactoring, DIALOG_BASED_USER_INTERFACE
				| PREVIEW_EXPAND_FIRST_NODE);
		setDefaultPageTitle(pageTitle);
	}

	@Override
	protected void addUserInputPages() {
		addPage(new RefactoringDataInputPage("IntroduceIndirectionInputPage"));
	}

}
