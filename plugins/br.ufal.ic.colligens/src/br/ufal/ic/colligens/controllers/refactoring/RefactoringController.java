package br.ufal.ic.colligens.controllers.refactoring;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.eclipse.ltk.core.refactoring.Refactoring;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.swt.widgets.Display;

import br.ufal.ic.colligens.controllers.ProjectExplorerController;
import br.ufal.ic.colligens.controllers.ProjectExplorerException;
import br.ufal.ic.colligens.controllers.invalidconfigurations.InvalidConfigurationsViewController;
import br.ufal.ic.colligens.models.TypeChef;
import br.ufal.ic.colligens.models.TypeChefException;

public class RefactoringController extends Refactoring {
	private ProjectExplorerController projectExplorerController;
	protected List<Change> changes = new LinkedList<Change>();

	public RefactoringController() {
		projectExplorerController = new ProjectExplorerController();
	}

	@Override
	public String getName() {
		return "Colligens Refactoring";
	}

	@Override
	public RefactoringStatus checkInitialConditions(IProgressMonitor monitor)
			throws CoreException, OperationCanceledException {
		RefactoringStatus status = new RefactoringStatus();
		try {
			monitor.beginTask("Checking preconditions...", 1);

			projectExplorerController.run();

			final TypeChef typeChef = new TypeChef();

			typeChef.run(projectExplorerController.getList());

			if (!typeChef.isFinish() || !typeChef.getFilesLog().isEmpty()) {
				status.addFatalError("This files contains errors in some feature combinations.");

				Display.getDefault().syncExec(new Runnable() {
					public void run() {

						InvalidConfigurationsViewController viewController = InvalidConfigurationsViewController
								.getInstance();
						viewController.showView();
						viewController.setInput(typeChef.getFilesLog());
					}
				});

			}
		} catch (TypeChefException e) {
			status.addFatalError(e.getMessage());
		} catch (ProjectExplorerException e) {
			// TODO Auto-generated catch block
			status.addFatalError(e.getMessage());
		} finally {
			monitor.done();
		}
		return status;
	}

	@Override
	public RefactoringStatus checkFinalConditions(IProgressMonitor monitor)
			throws CoreException, OperationCanceledException {
		RefactoringStatus status = new RefactoringStatus();

		monitor.beginTask("Checking checkFinalConditions...", 2);
		RefactoringProcessor processor = new RefactoringProcessor();
		processor.setiResources(projectExplorerController.getList());

		changes = processor.process(monitor);

		return status;
	}

	@Override
	public Change createChange(IProgressMonitor pm) throws CoreException,
			OperationCanceledException {
		try {
			pm.beginTask("Creating change...", 1);

			//
			Change[] changeArray = changes.toArray(new Change[] {});
			//
			return new CompositeChange(getName(), changeArray);
		} finally {
			pm.done();
		}
	}

	public void setSelection(IStructuredSelection selection) {
		projectExplorerController.setSelection(selection);
	}

}
