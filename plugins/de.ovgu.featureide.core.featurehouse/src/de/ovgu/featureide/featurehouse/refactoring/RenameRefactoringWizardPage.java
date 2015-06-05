package de.ovgu.featureide.featurehouse.refactoring;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.ltk.ui.refactoring.UserInputWizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;


public class RenameRefactoringWizardPage extends UserInputWizardPage {
	
	private static final String PAGE_NAME = "ExampleRefactoringInputPage";	
	private final RenameMethodRefactoring refactoring;
	private boolean initialized = false;
	private Text methodName;
	
	public RenameRefactoringWizardPage(RenameRefactoringWizard wizard) {
		super(PAGE_NAME);
		refactoring = (RenameMethodRefactoring) wizard.getRefactoring();
	}
	
	@Override
	public void createControl(Composite parent) {
		initializeDialogUnits(parent);
		Composite composite = new Composite(parent, SWT.NONE);
		setControl(composite);
		GridLayout gridLayout = new GridLayout(2, false);
		composite.setLayout(gridLayout);
	}
	
	@Override
	public void setVisible(boolean visible) {
		if (visible && !initialized) {
			initialized = true;
			Composite composite = (Composite) getControl();
			addElements(composite);
			Dialog.applyDialogFont(composite);
		}
		super.setVisible(visible);
	}
	
	private void addElements(Composite composite) {
		Label label= new Label(composite, SWT.NONE);
		label.setText("&New name:");

		methodName = new Text(composite, SWT.SINGLE | SWT.LEFT | SWT.BORDER);
		methodName.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		methodName.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent event) {
				methodeNameChanged();
			}
		});
			
		methodName.setFocus();
		methodName.selectAll();
		methodeNameChanged();		
	}
	
	void methodeNameChanged() {
//		RefactoringStatus status = new RefactoringStatus();
//		
//		status.merge(refactoring.setMethodName(methodName.getText()));
//
//		setPageComplete(!status.hasError());
//		int severity = status.getSeverity();
//		String message = status.getMessageMatchingSeverity(severity);
//		if (severity >= RefactoringStatus.INFO) {
//			setMessage(message, severity);
//		} else {
//			setMessage("", NONE); //$NON-NLS-1$
//		}
	}	
}