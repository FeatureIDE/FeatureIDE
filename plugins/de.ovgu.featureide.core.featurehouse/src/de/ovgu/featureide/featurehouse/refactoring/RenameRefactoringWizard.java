package de.ovgu.featureide.featurehouse.refactoring;

import org.eclipse.ltk.ui.refactoring.RefactoringWizard;

import de.ovgu.featureide.core.signature.base.AbstractSignature;

public class RenameRefactoringWizard extends RefactoringWizard {

	public RenameRefactoringWizard(final RenameRefactoring<AbstractSignature> refactoring) {
		super(refactoring, DIALOG_BASED_USER_INTERFACE | CHECK_INITIAL_CONDITIONS_ON_OPEN | PREVIEW_EXPAND_FIRST_NODE | NO_BACK_BUTTON_ON_STATUS_DIALOG);
		setDefaultPageTitle(refactoring.getName());
	}

	@Override
	protected void addUserInputPages() {
		addPage(new RenameRefactoringWizardPage(this));
	}
}
