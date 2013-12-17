package br.ufal.ic.colligens.controllers.refactoring;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.eclipse.ltk.core.refactoring.Refactoring;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.PlatformUI;

import br.ufal.ic.colligens.models.FileProxy;
import br.ufal.ic.colligens.util.Log;
import br.ufal.ic.colligens.views.InvalidConfigurationsView;
import de.fosd.typechef.lexer.LexerException;
import de.fosd.typechef.lexer.options.OptionException;

public class RefactorSelectionController extends Refactoring {
	private TextSelection textSelection = null;
	private IFile file = null;
	private RefactorSelectionProcessor processor;
	protected List<Change> changes = new LinkedList<Change>();

	public RefactorSelectionController() {
		processor = new RefactorSelectionProcessor();
	}

	@Override
	public String getName() {
		return "Refactoring Undisciplined";
	}

	@Override
	public RefactoringStatus checkInitialConditions(IProgressMonitor monitor)
			throws CoreException, OperationCanceledException {
		RefactoringStatus status = new RefactoringStatus();

		monitor.beginTask("Checking preconditions...", 2);

		try {

			processor.selectToFile(file, textSelection);

		} catch (LexerException e) {
			status.addFatalError("Was not possible to refactor the selected part.");

		} catch (OptionException e) {
			status.addFatalError("Was not possible to refactor. Try again.");

		} catch (IOException e) {
			status.addFatalError("Was not possible to refactor the selected part. Try again.");

		} catch (NullPointerException e) {
			status.addFatalError("Was not possible to refactor the selected part.");

		} catch (RefactorException e) {
			status.addFatalError("The selected part contains errors.");
		} finally {
			if (processor.fileProxy != null
					&& !processor.fileProxy.getLogs().isEmpty()) {

				Display.getDefault().asyncExec(new Runnable() {
					public void run() {

						IViewPart view = PlatformUI.getWorkbench()
								.getActiveWorkbenchWindow().getActivePage()
								.findView(InvalidConfigurationsView.ID);
						if (view instanceof InvalidConfigurationsView) {
							final InvalidConfigurationsView analyzerView = (InvalidConfigurationsView) view;

							List<FileProxy> list = new LinkedList<FileProxy>();

							for (Log log : processor.fileProxy.getLogs()) {
								log.setSelection(textSelection);
							}

							list.add(processor.fileProxy);
							// returns the list to view
							analyzerView.setInput(list);

						}
					}
				});
			}
		}

		monitor.done();

		return status;
	}

	@Override
	public RefactoringStatus checkFinalConditions(IProgressMonitor monitor)
			throws CoreException, OperationCanceledException {
		RefactoringStatus status = new RefactoringStatus();

		monitor.beginTask("Checking checkFinalConditions...", 2);

		try {
			changes = processor.process(textSelection, monitor);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			status.addFatalError(e.getMessage());
			e.printStackTrace();
		}

		return status;
	}

	@Override
	public Change createChange(IProgressMonitor pm) throws CoreException,
			OperationCanceledException {
		try {
			pm.beginTask("Creating change...", 1);
			Change[] changeArray = changes.toArray(new Change[] {});
			//
			return new CompositeChange(getName(), changeArray);
		} finally {
			pm.done();
		}
	}

	public void setSelection(IFile file, TextSelection selection) {
		this.textSelection = selection;
		this.file = file;
	}

}
