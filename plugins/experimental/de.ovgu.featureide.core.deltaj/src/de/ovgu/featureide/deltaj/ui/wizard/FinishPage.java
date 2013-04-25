package de.ovgu.featureide.deltaj.ui.wizard;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.events.MouseAdapter;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.layout.FillLayout;

public class FinishPage extends WizardPage {

	DeltaJNewProjectWizardExtension extension;
	
	/**
	 * Create the wizard.
	 */
	public FinishPage(DeltaJNewProjectWizardExtension extension) {
		super("finishPage");
		this.extension = extension;
		setTitle("Finish DeltaJ Feature Wizard");
		setDescription("Select initial properties.");
	}

	/**
	 * Create contents of the wizard.
	 * @param parent
	 */
	public void createControl(Composite parent) {
		Composite container = new Composite(parent, SWT.NULL);

		setControl(container);
		container.setLayout(new FillLayout(SWT.HORIZONTAL));
		
		Button btnCreateSeperateFiles = new Button(container, SWT.CHECK);
		btnCreateSeperateFiles.addMouseListener(new MouseAdapter() {
			@Override
			public void mouseDown(MouseEvent e) {
				extension.setCreatesSeperateFiles(!extension.isCreatesSeperateFiles());
			}
		});
		btnCreateSeperateFiles.setText("Create seperate .deltaj files for each selected feature.");
	}

	@Override
	public void setVisible(boolean visible) {
		// TODO Auto-generated method stub
		super.setVisible(visible);
		extension.setFinished(true);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.wizard.WizardPage#canFlipToNextPage()
	 */
	@Override
	public boolean canFlipToNextPage() {
		return false;
	}
}
