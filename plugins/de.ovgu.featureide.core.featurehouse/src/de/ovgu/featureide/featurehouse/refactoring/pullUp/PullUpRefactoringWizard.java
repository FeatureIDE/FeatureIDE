package de.ovgu.featureide.featurehouse.refactoring.pullUp;

import org.eclipse.ltk.ui.refactoring.RefactoringWizard;

public class PullUpRefactoringWizard extends RefactoringWizard {

	public PullUpRefactoringWizard(final PullUpRefactoring refactoring) {
		super(refactoring, WIZARD_BASED_USER_INTERFACE);
		setDefaultPageTitle(refactoring.getName());
	}

	@Override
	protected void addUserInputPages() {
		addPage(new PullUpMemberPage(this));
	}

}
