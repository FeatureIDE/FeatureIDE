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

import core.RefactoringType;
import de.fosd.typechef.lexer.LexerException;
import de.fosd.typechef.options.OptionException;

public class RefactorSelectionController extends Refactoring {
	private TextSelection textSelection = null;
	private IFile file = null;
	private RefactoringType refactoringType;
	private final RefactorSelectionProcessor processor;
	protected List<Change> changes = new LinkedList<Change>();

	public RefactorSelectionController() {
		processor = new RefactorSelectionProcessor();
	}

	@Override
	public String getName() {
		return "Refactoring " + refactoringType.getLabel();
	}

	@Override
	public RefactoringStatus checkInitialConditions(IProgressMonitor monitor)
			throws CoreException, OperationCanceledException {
		RefactoringStatus status = new RefactoringStatus();
		
		monitor.beginTask("Checking preconditions...", 2);

		try {

			processor.selectToFile(file, textSelection, refactoringType);

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
			monitor.done();
		}
		return status;
	}

	@Override
	public RefactoringStatus checkFinalConditions(IProgressMonitor monitor)
			throws CoreException, OperationCanceledException {
		RefactoringStatus status = new RefactoringStatus();

		monitor.beginTask("Checking checkFinalConditions...", 2);

		try {
			changes = processor.process(monitor);
		} catch (IOException e) {

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
			//
			return new CompositeChange(getName(),
					changes.toArray(new Change[] {}));
		} finally {
			pm.done();
		}
	}

	public void setSelection(IFile file, TextSelection selection,
			RefactoringType refactoringType) {
		this.textSelection = selection;
		this.file = file;
		this.refactoringType = refactoringType;
	}

}
