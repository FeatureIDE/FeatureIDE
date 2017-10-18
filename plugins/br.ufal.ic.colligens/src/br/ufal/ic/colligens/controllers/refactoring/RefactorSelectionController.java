package br.ufal.ic.colligens.controllers.refactoring;

import static de.ovgu.featureide.fm.core.localization.StringTable.CHECKING_CHECKFINALCONDITIONS___;
import static de.ovgu.featureide.fm.core.localization.StringTable.CHECKING_PRECONDITIONS___;
import static de.ovgu.featureide.fm.core.localization.StringTable.CREATING_CHANGE___;
import static de.ovgu.featureide.fm.core.localization.StringTable.REFACTORING;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_SELECTED_PART_CONTAINS_ERRORS_;
import static de.ovgu.featureide.fm.core.localization.StringTable.WAS_NOT_POSSIBLE_TO_REFACTOR_THE_SELECTED_PART_;
import static de.ovgu.featureide.fm.core.localization.StringTable.WAS_NOT_POSSIBLE_TO_REFACTOR_THE_SELECTED_PART__TRY_AGAIN_;
import static de.ovgu.featureide.fm.core.localization.StringTable.WAS_NOT_POSSIBLE_TO_REFACTOR__TRY_AGAIN_;

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
		return REFACTORING + refactoringType.getLabel();
	}

	@Override
	public RefactoringStatus checkInitialConditions(IProgressMonitor monitor) throws CoreException, OperationCanceledException {
		final RefactoringStatus status = new RefactoringStatus();

		monitor.beginTask(CHECKING_PRECONDITIONS___, 2);

		try {

			processor.selectToFile(file, textSelection, refactoringType);

		} catch (final LexerException e) {
			status.addFatalError(WAS_NOT_POSSIBLE_TO_REFACTOR_THE_SELECTED_PART_);

		} catch (final OptionException e) {
			status.addFatalError(WAS_NOT_POSSIBLE_TO_REFACTOR__TRY_AGAIN_);

		} catch (final IOException e) {
			status.addFatalError(WAS_NOT_POSSIBLE_TO_REFACTOR_THE_SELECTED_PART__TRY_AGAIN_);

		} catch (final NullPointerException e) {
			status.addFatalError(WAS_NOT_POSSIBLE_TO_REFACTOR_THE_SELECTED_PART_);

		} catch (final RefactorException e) {
			status.addFatalError(THE_SELECTED_PART_CONTAINS_ERRORS_);
		} finally {
			monitor.done();
		}
		return status;
	}

	@Override
	public RefactoringStatus checkFinalConditions(IProgressMonitor monitor) throws CoreException, OperationCanceledException {
		final RefactoringStatus status = new RefactoringStatus();

		monitor.beginTask(CHECKING_CHECKFINALCONDITIONS___, 2);

		try {
			changes = processor.process(monitor);
		} catch (final IOException e) {

			status.addFatalError(e.getMessage());
			e.printStackTrace();
		}

		return status;
	}

	@Override
	public Change createChange(IProgressMonitor pm) throws CoreException, OperationCanceledException {
		try {
			pm.beginTask(CREATING_CHANGE___, 1);
			//
			return new CompositeChange(getName(), changes.toArray(new Change[] {}));
		} finally {
			pm.done();
		}
	}

	public void setSelection(IFile file, TextSelection selection, RefactoringType refactoringType) {
		textSelection = selection;
		this.file = file;
		this.refactoringType = refactoringType;
	}

}
