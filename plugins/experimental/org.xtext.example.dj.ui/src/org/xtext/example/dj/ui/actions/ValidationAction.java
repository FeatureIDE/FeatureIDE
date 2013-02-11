package org.xtext.example.dj.ui.actions;

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.xtext.example.util.DJIdeProperties;
import org.xtext.example.util.ValidationStatus;

/**
 * Our sample action implements workbench action delegate.
 * The action proxy will be created by the workbench and
 * shown in the UI. When the user tries to use the action,
 * this delegate will be created and execution will be 
 * delegated to it.
 * @see IWorkbenchWindowActionDelegate
 */
public class ValidationAction implements IWorkbenchWindowActionDelegate {
	@SuppressWarnings("unused")
	private IWorkbenchWindow window;
	
	private static final String VALIDATE_ALL_ID = "org.xtext.example.dj.ui.actions.ValidateAll";
	private static final String PARTIAL_VALIDATION_ID = "org.xtext.example.dj.ui.actions.PartialValidation";
	private static final String SINTAX_VALIDATION_ID = "org.xtext.example.dj.ui.actions.SyntaxOnly";
	
	/**
	 * The constructor.
	 */
	public ValidationAction() {
	}

	/**
	 * The action has been activated. The argument of the
	 * method represents the 'real' action sitting
	 * in the workbench UI.
	 * @see IWorkbenchWindowActionDelegate#run
	 */
	public void run(IAction action) {
		if (action.getId().equals(VALIDATE_ALL_ID)) {
			DJIdeProperties.changeValidationStatus(ValidationStatus.VALIDATE_ALL);
		} else if (action.getId().equals(PARTIAL_VALIDATION_ID)) {
			DJIdeProperties.changeValidationStatus(ValidationStatus.PARTIAL_VALIDATION);
		} else if (action.getId().equals(SINTAX_VALIDATION_ID)) {
			DJIdeProperties.changeValidationStatus(ValidationStatus.SYNTAX_ONLY);
		}
	}

	/**
	 * Selection in the workbench has been changed. We 
	 * can change the state of the 'real' action here
	 * if we want, but this can only happen after 
	 * the delegate has been created.
	 * @see IWorkbenchWindowActionDelegate#selectionChanged
	 */
	public void selectionChanged(IAction action, ISelection selection) {
	}

	/**
	 * We can use this method to dispose of any system
	 * resources we previously allocated.
	 * @see IWorkbenchWindowActionDelegate#dispose
	 */
	public void dispose() {
	}

	/**
	 * We will cache window object in order to
	 * be able to provide parent shell for the message dialog.
	 * @see IWorkbenchWindowActionDelegate#init
	 */
	public void init(IWorkbenchWindow window) {
		this.window = window;
	}
}