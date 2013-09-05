package br.ufal.ic.colligens.controllers.refactoring;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.cdt.core.model.CoreModel;
import org.eclipse.cdt.core.model.ITranslationUnit;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.text.edits.InsertEdit;
import org.eclipse.text.edits.MultiTextEdit;

public class RefactoringProcessor {
	private List<IResource> iResources;
	// List of change perform on the code
	protected List<Change> changes = new LinkedList<Change>();

	public List<IResource> getiResources() {
		return iResources;
	}

	public void setiResources(List<IResource> iResources) {
		this.iResources = iResources;
	}

	public List<Change> process(IProgressMonitor monitor) throws CoreException {

		for (IResource resource : iResources) {
			ITranslationUnit tu = (ITranslationUnit) CoreModel.getDefault()
					.create((IFile) resource);

			MultiTextEdit edit = new MultiTextEdit();

			// edit.addChild(new ReplaceEdit(0, 50,"novo texto"));
			edit.addChild(new InsertEdit(0, "/*"));
			edit.addChild(new InsertEdit(0, " Refactoring Colligens "));

			String name = tu.getElementName();
			IFile ifile2 = (IFile) tu.getResource();
			TextFileChange change = new TextFileChange(name, ifile2);

			change.setTextType("c");
			change.setEdit(edit);
			changes.add(change);

		}

		return changes;
	}

}
