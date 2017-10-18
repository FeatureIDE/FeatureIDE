package br.ufal.ic.colligens.controllers.refactoring;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.text.edits.MultiTextEdit;
import org.eclipse.text.edits.ReplaceEdit;

import br.ufal.ic.colligens.models.PlatformException;
import br.ufal.ic.colligens.models.StubsHeader;
import core.RefactoringFrontend;
import core.RefactoringType;
import de.fosd.typechef.lexer.LexerException;
import de.fosd.typechef.options.OptionException;

public class RefactorSelectionProcessor {

	private String sourceOutRefactor;
	private TextSelection textSelection = null;
	private IFile file = null;
	private StubsHeader stubsHeader;
	// List of change perform on the code
	protected List<Change> changes = new LinkedList<Change>();

	public void selectToFile(IFile file, TextSelection textSelection, RefactoringType refactoringType)
			throws IOException, LexerException, OptionException, RefactorException {

		this.textSelection = textSelection;
		this.file = file;

		stubsHeader = new StubsHeader();

		try {
			stubsHeader.setProject(file.getProject().getName());
			stubsHeader.run();
		} catch (final PlatformException e) {
			e.printStackTrace();
			throw new RefactorException();
		}

		final RefactoringFrontend refactoring = new RefactoringFrontend();

		sourceOutRefactor = refactoring.refactorCode(textSelection.getText(), stubsHeader.getIncludePath(), refactoringType);

		removeStubs();

		if (sourceOutRefactor == null) {
			throw new RefactorException();
		}

	}

	public List<Change> process(IProgressMonitor monitor) throws IOException {

		final MultiTextEdit edit = new MultiTextEdit();

		edit.addChild(new ReplaceEdit(textSelection.getOffset(), textSelection.getLength(), sourceOutRefactor));

		final TextFileChange change = new TextFileChange(file.getName(), file);

		change.setTextType("c");
		change.setEdit(edit);
		changes.add(change);

		return changes;
	}

	public void removeStubs() throws IOException {

		final Collection<String> collection = stubsHeader.getIncludes();

		for (final Iterator<String> iterator = collection.iterator(); iterator.hasNext();) {
			final BufferedReader br = new BufferedReader(new FileReader(iterator.next()));
			try {
				String line = br.readLine();
				while ((line != null) && line.contains("typedef")) {
					sourceOutRefactor = sourceOutRefactor.replace(line + "\n", "");
					line = br.readLine();
				}
			} finally {
				br.close();
			}
		}

	}
}
