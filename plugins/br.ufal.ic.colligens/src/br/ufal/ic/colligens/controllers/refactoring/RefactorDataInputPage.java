package br.ufal.ic.colligens.controllers.refactoring;

import static de.ovgu.featureide.fm.core.localization.StringTable.THIS_IS_A_LABEL;

import org.eclipse.ltk.ui.refactoring.UserInputWizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;

public class RefactorDataInputPage extends UserInputWizardPage {

	public RefactorDataInputPage(String name) {
		super(name);
	}

	@Override
	public void createControl(Composite parent) {
		final Composite result = new Composite(parent, SWT.NONE);
		final GridData gridData = new GridData(SWT.FILL, SWT.FILL, true, false);
		gridData.horizontalSpan = 2;
		result.setLayoutData(gridData);
		result.setLayout(new GridLayout(1, false));

		final Label label = new Label(result, SWT.NONE);
		label.setText(THIS_IS_A_LABEL);
		// Create new layout data
		final GridData data = new GridData(SWT.FILL, SWT.LEFT, true, false, 2, 1);
		label.setLayoutData(data);

		setControl(result);
	}

}
