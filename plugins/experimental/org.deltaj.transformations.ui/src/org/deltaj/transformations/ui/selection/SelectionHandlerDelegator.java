package org.deltaj.transformations.ui.selection;

import org.eclipse.xtext.ui.editor.XtextEditor;
import org.eclipse.xtext.ui.editor.model.IXtextDocument;
import org.eclipse.xtext.ui.editor.utils.EditorUtils;

public class SelectionHandlerDelegator {

	private final DeltaJSelection selection;

	public SelectionHandlerDelegator(DeltaJSelection selection) {

		this.selection = selection;
	}

	public <R> R delegate(IReadOnlySelectionHandler<R> selectionHandler) {

		IXtextDocument document = getDocument();

		if (document != null) {
			return document.readOnly(new UnitOfWorkOnSelection<R>(selection, selectionHandler));
		} else {
			return null;
		}
	}

	public <R> R delegate(IModifyingSelectionHandler<R> selectionHandler) {

		IXtextDocument document = getDocument();

		if (document != null) {
			return document.modify(new UnitOfWorkOnSelection<R>(selection, selectionHandler));
		} else {
			return null;
		}
	}

	private IXtextDocument getDocument() {

		XtextEditor xtextEditor = EditorUtils.getActiveXtextEditor();
		return xtextEditor != null? xtextEditor.getDocument() : null;
	}
}
