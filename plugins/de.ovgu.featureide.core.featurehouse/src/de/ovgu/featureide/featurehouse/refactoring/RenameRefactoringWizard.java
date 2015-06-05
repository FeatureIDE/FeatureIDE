package de.ovgu.featureide.featurehouse.refactoring;

import org.eclipse.ltk.ui.refactoring.RefactoringWizard;

public class RenameRefactoringWizard extends RefactoringWizard {

    public RenameRefactoringWizard(RenameMethodRefactoring refactoring) {
		super(refactoring, DIALOG_BASED_USER_INTERFACE | CHECK_INITIAL_CONDITIONS_ON_OPEN | PREVIEW_EXPAND_FIRST_NODE | NO_BACK_BUTTON_ON_STATUS_DIALOG );
		setDefaultPageTitle("Rename Method"); 
	}
    
	@Override
    protected void addUserInputPages(){		
		addPage(new RenameRefactoringWizardPage(this));
	}
}
