package br.ufal.ic.colligens.controllers.refactoring;

import org.eclipse.ltk.ui.refactoring.UserInputWizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;

public class RefactoringDataInputPage extends UserInputWizardPage {

	public RefactoringDataInputPage(String name) {
		super(name);
	}

	@Override
	public void createControl(Composite parent) {
		Composite result = new Composite(parent, SWT.NONE);
		setControl(result);
	}

}
