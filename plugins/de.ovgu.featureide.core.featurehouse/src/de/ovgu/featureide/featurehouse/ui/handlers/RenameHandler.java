package de.ovgu.featureide.featurehouse.ui.handlers;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.ltk.ui.refactoring.RefactoringWizardOpenOperation;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.texteditor.ITextEditor;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.featurehouse.refactoring.FujiSelector;
import de.ovgu.featureide.featurehouse.refactoring.RenameFieldRefactoring;
import de.ovgu.featureide.featurehouse.refactoring.RenameLocalVariableRefactoring;
import de.ovgu.featureide.featurehouse.refactoring.RenameMethodRefactoring;
import de.ovgu.featureide.featurehouse.refactoring.RenameRefactoring;
import de.ovgu.featureide.featurehouse.refactoring.RenameRefactoringWizard;
import de.ovgu.featureide.featurehouse.refactoring.RenameTypeRefactoring;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiClassSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiFieldSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiLocalVariableSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;

public class RenameHandler extends RefactoringHandler {

	@Override
	protected void singleAction(Object element, String file) {
		try {
			IFeatureProject featureProject = getFeatureProject();
			if (featureProject == null) return;

			RenameRefactoring refactoring;
			if (element instanceof FujiMethodSignature) {
				FujiMethodSignature method = (FujiMethodSignature) element;

				if (method.isConstructor()) refactoring = new RenameTypeRefactoring((FujiClassSignature) method.getParent(), featureProject, file);
				else refactoring = new RenameMethodRefactoring(method, featureProject, file);
			} else if (element instanceof FujiClassSignature) {
				refactoring = new RenameTypeRefactoring((FujiClassSignature) element, featureProject, file);
			} else if (element instanceof FujiFieldSignature) {
				refactoring = new RenameFieldRefactoring((FujiFieldSignature) element, featureProject, file);
			} else if (element instanceof FujiLocalVariableSignature) {
				refactoring = new RenameLocalVariableRefactoring((FujiLocalVariableSignature) element, featureProject, file);
			} else return;

			RenameRefactoringWizard refactoringWizard = new RenameRefactoringWizard(refactoring);
			RefactoringWizardOpenOperation op = new RefactoringWizardOpenOperation(refactoringWizard);
			op.run(getShell(), "Rename-Refactoring");
		} catch (InterruptedException e) {}
	}

	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		IWorkbenchPage page = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
		ITextEditor editor = (ITextEditor) page.getActiveEditor();

		IJavaElement elem = JavaUI.getEditorInputJavaElement(editor.getEditorInput());
		if (elem instanceof ICompilationUnit) {
			ITextSelection sel = (ITextSelection) editor.getSelectionProvider().getSelection();

			IDocument document = editor.getDocumentProvider().getDocument(editor.getEditorInput());

			int lineOffset = 0;
			try {
				lineOffset = document.getLineOffset(sel.getStartLine());
			} catch (BadLocationException e1) {
				e1.printStackTrace();
			}
			int column = sel.getOffset() - lineOffset;

			final String file = ((ICompilationUnit) elem).getResource().getRawLocation().toOSString();

			IFeatureProject featureProject = getFeatureProject();
			createSignatures(featureProject);

			FujiSelector selector = new FujiSelector(featureProject, file);
			AbstractSignature signature = selector.getSelectedSignature(sel.getStartLine() + 1, column);
			if (signature != null) singleAction(signature, file);
		}

		return null;
	}
}
