package de.ovgu.featureide.featurehouse.ui.handlers;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.ltk.ui.refactoring.RefactoringWizardOpenOperation;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.texteditor.ITextEditor;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.featurehouse.refactoring.FujiSelector;
import de.ovgu.featureide.featurehouse.refactoring.pullUp.PullUpRefactoring;
import de.ovgu.featureide.featurehouse.refactoring.pullUp.PullUpRefactoringWizard;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiClassSignature;

public class PullUpHandler extends RefactoringHandler {

	protected void singleAction(Object element, String file) {
		try {
			IFeatureProject featureProject = getFeatureProject();
			if (featureProject == null) return;

			PullUpRefactoring pullUp = new PullUpRefactoring((FujiClassSignature) element, featureProject, file);
			PullUpRefactoringWizard refactoringWizard = new PullUpRefactoringWizard(pullUp);
			RefactoringWizardOpenOperation op = new RefactoringWizardOpenOperation(refactoringWizard);
			op.run(getShell(), "PullUp-Refactoring");
		} catch (InterruptedException e) {}
	}

	@Override
	public final Object execute(ExecutionEvent event) throws ExecutionException {
		IWorkbenchPage page = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
		ITextEditor editor = (ITextEditor) page.getActiveEditor();

		IJavaElement elem = JavaUI.getEditorInputJavaElement(editor.getEditorInput());
		if (elem instanceof ICompilationUnit) {
			final String file = ((ICompilationUnit) elem).getResource().getRawLocation().toOSString();

			IFeatureProject featureProject = getFeatureProject();
			createSignatures(featureProject);

			FujiSelector selector = new FujiSelector(featureProject, file);
			AbstractSignature signature = selector.getSelectedClassSignature();
			if (signature != null) singleAction(signature, file);
		}

		return null;
	}

}
