package de.ovgu.featureide.featurehouse.ui.handlers;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ltk.ui.refactoring.RefactoringWizardOpenOperation;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.ide.ResourceUtil;
import org.eclipse.ui.texteditor.ITextEditor;

import de.ovgu.featureide.core.CorePlugin;
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
import de.ovgu.featureide.fm.ui.handlers.base.ASelectionHandler;


public class RenameHandler extends ASelectionHandler {

	@Override
	protected void singleAction(Object element) 
	{
		try {
			IFeatureProject featureProject = getFeatureProject();
			if (featureProject == null)
				return;

			RenameRefactoring refactoring;
			if (element instanceof FujiMethodSignature){
				FujiMethodSignature method = (FujiMethodSignature) element;

				if (method.isConstructor())
					refactoring = new RenameTypeRefactoring((FujiClassSignature)method.getParent(), featureProject);
				else
					refactoring = new RenameMethodRefactoring(method, featureProject);
			} else if (element instanceof FujiClassSignature){
				refactoring = new RenameTypeRefactoring((FujiClassSignature) element, featureProject);
			} else if (element instanceof FujiFieldSignature){
				refactoring = new RenameFieldRefactoring((FujiFieldSignature) element, featureProject);
			} else if (element instanceof FujiLocalVariableSignature){
				refactoring = new RenameLocalVariableRefactoring((FujiLocalVariableSignature) element, featureProject);
			} else
				return;

			RenameRefactoringWizard refactoringWizard = new RenameRefactoringWizard(refactoring);
			RefactoringWizardOpenOperation op = new RefactoringWizardOpenOperation(refactoringWizard);
			op.run(getShell(), "Rename-Refactoring");
		} catch (InterruptedException e) {
		}
	}

	protected Shell getShell() 
	{
		IWorkbenchWindow window = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		if (window == null) return null;
		return window.getShell();
	}
	
	
	@Override
	public final Object execute(ExecutionEvent event) throws ExecutionException {
		ISelection selection = HandlerUtil.getCurrentSelection(event);
		if (selection instanceof ITextSelection)
		{
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
				
				FujiSelector selector = new FujiSelector(getFeatureProject(), file);
				AbstractSignature signature = selector.getSelectedSignature(sel.getStartLine()+1, column);
				if (signature != null) 					
					singleAction(signature);
			}
		}
		
		return null;
	}
	
	protected IFeatureProject getFeatureProject()
	{
		IEditorInput fileEditorInput = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor().getEditorInput();
		final IFile file = ResourceUtil.getFile(fileEditorInput);
		if (file == null) return null;
		
		return CorePlugin.getFeatureProject(file);
	}

}
