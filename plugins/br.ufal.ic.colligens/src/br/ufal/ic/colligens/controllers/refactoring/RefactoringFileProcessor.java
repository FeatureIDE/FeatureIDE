package br.ufal.ic.colligens.controllers.refactoring;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.filebuffers.FileBuffers;
import org.eclipse.core.filebuffers.ITextFileBufferManager;
import org.eclipse.core.filebuffers.LocationKind;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.text.edits.MultiTextEdit;
import org.eclipse.text.edits.ReplaceEdit;

import test.TestTypeChef;
import de.fosd.typechef.lexer.LexerException;
import de.fosd.typechef.lexer.options.OptionException;

public class RefactoringFileProcessor {
	private List<IResource> iResources;
	// List of change perform on the code
	protected List<Change> changes = new LinkedList<Change>();

	public List<IResource> getiResources() {
		return iResources;
	}

	public void setiResources(List<IResource> iResources) {
		this.iResources = iResources;
	}

	public List<Change> process(IProgressMonitor monitor) throws CoreException,
			IOException {
		// Class from
		TestTypeChef chef = new TestTypeChef();

		for (IResource resource : iResources) {
			ITextFileBufferManager.DEFAULT.connect(resource.getFullPath(),
					LocationKind.IFILE, null);
			IDocument document = FileBuffers
					.getTextFileBufferManager()
					.getTextFileBuffer(resource.getFullPath(),
							LocationKind.IFILE).getDocument();

			String outFilePath = null;
			try {

				outFilePath = chef.refactoringFile(resource.getLocation()
						.toOSString());

			} catch (LexerException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (OptionException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}

			File file = new File(outFilePath);

			String sourceOut = "";

			FileReader fileR = new FileReader(file);
			BufferedReader buffR = new BufferedReader(fileR);

			String line;
			while ((line = buffR.readLine()) != null) {
				sourceOut = sourceOut + line + "\n";
			}

			buffR.close();

			MultiTextEdit edit = new MultiTextEdit();

			edit.addChild(new ReplaceEdit(0, document.getLength(), sourceOut));

			TextFileChange change = new TextFileChange(resource.getName(),
					(IFile) resource);

			change.setTextType("c");
			change.setEdit(edit);
			changes.add(change);

		}

		return changes;
	}
}
