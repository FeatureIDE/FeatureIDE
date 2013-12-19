package br.ufal.ic.colligens.controllers.refactoring;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.text.edits.MultiTextEdit;
import org.eclipse.text.edits.ReplaceEdit;

import br.ufal.ic.colligens.models.FileProxy;
import br.ufal.ic.colligens.refactoring.core.RefactoringsFrondEnd;
import de.fosd.typechef.lexer.LexerException;
import de.fosd.typechef.lexer.options.OptionException;

//TODO 
public class RefactorSelectionProcessor {
	protected FileProxy fileProxy = null;
	// List of change perform on the code
	protected List<Change> changes = new LinkedList<Change>();

	public void selectToFile(IFile ifile, TextSelection textSelection)
			throws IOException, LexerException, OptionException,
			RefactorException {

		fileProxy = new FileProxy(ifile);

		String filePath = System.getProperty("java.io.tmpdir") + "/"
				+ this.hashCode() + ".c";
		RandomAccessFile arq = new RandomAccessFile(filePath, "rw");

		arq.close();

		File file = new File(filePath);

		FileWriter fileW = new FileWriter(file);
		BufferedWriter buffW = new BufferedWriter(fileW);

		buffW.write(textSelection.getText());

		buffW.close();
		fileW.close();

		RefactoringsFrondEnd refactoring = new RefactoringsFrondEnd();

		fileProxy.setFileToAnalyse(filePath);

		refactoring.refactoringFile(fileProxy);

	}

	public List<Change> process(TextSelection textSelection,
			IProgressMonitor monitor) throws IOException {

		File file = new File(fileProxy.getFileToAnalyse());

		String sourceOut = "";

		FileReader fileR = new FileReader(file);
		BufferedReader buffR = new BufferedReader(fileR);

		String line;
		while ((line = buffR.readLine()) != null) {
			sourceOut = sourceOut + line + "\n";
		}

		buffR.close();
		fileR.close();

		MultiTextEdit edit = new MultiTextEdit();

		edit.addChild(new ReplaceEdit(textSelection.getOffset(), textSelection
				.getLength(), sourceOut));

		TextFileChange change = new TextFileChange(fileProxy.getFileName(),
				(IFile) fileProxy.getResource());

		change.setTextType("c");
		change.setEdit(edit);
		changes.add(change);

		return changes;
	}

}
