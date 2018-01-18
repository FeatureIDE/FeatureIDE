/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 *
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors;

import static de.ovgu.featureide.fm.core.localization.StringTable.SOURCE;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.IUndoContext;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.IDocument;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.editors.text.TextEditor;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.SourceChangedOperation;

/**
 * Displays the source.
 *
 * @author Jens Meinicke
 * @author Marcus Pinnecke (Feature Interface)
 */
public class FeatureModelTextEditorPage extends TextEditor implements IFeatureModelEditorPage {

	private static final String ID = FMUIPlugin.PLUGIN_ID + ".editors.FeatureModelTextEditorPage";
	private static final String PAGE_TEXT = SOURCE;

	private final FeatureModelEditor featureModelEditor;
	private int index;

	private String oldText = null;

	public FeatureModelTextEditorPage(FeatureModelEditor featureModelEditor) {
		super();
		this.featureModelEditor = featureModelEditor;
	}

	@Override
	public int getIndex() {
		return index;
	}

	@Override
	public void setIndex(int index) {
		this.index = index;
	}

	@Override
	public String getPageText() {
		return PAGE_TEXT;
	}

	/**
	 * Updates the text editor from diagram.
	 */
	private void updateTextEditor() {
		final String text = featureModelEditor.fmManager.getFormat().getInstance().write(getFeatureModel());
		final IDocument document = getDocumentProvider().getDocument(getEditorInput());
		if (!document.get().equals(text)) {
			document.set(text);
		}
	}

	private IFeatureModel getFeatureModel() {
		return featureModelEditor.getFeatureModel();
	}

	/**
	 * Reads the current content of the model.xml file. (Removes dirty state for the page)
	 */
	public void resetTextEditor() {
		try {
			getDocumentProvider().resetDocument(getEditorInput());
		} catch (final CoreException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

	@Override
	public void initEditor() {}

	@Override
	protected void doSetInput(IEditorInput input) throws CoreException {
		super.doSetInput(input);
		oldText = getDocumentProvider().getDocument(input).get();
	}

	@Override
	public void doSave(IProgressMonitor progressMonitor) {
		super.doSave(progressMonitor);
		if (featureModelEditor.checkModel(getCurrentContent())) {
			executeSaveOperation();
		}
	}

	@Override
	public IFeatureModelEditorPage getPage(Composite container) {
		return this;
	}

	@Override
	public Control getControl() {
		return null;
	}

	@Override
	public void propertyChange(FeatureIDEEvent event) {}

	@Override
	public boolean allowPageChange(int newPage) {
		final String newText = getCurrentContent();
		return (newPage == getIndex()) || featureModelEditor.checkModel(newText);
	}

	@Override
	public void pageChangeFrom(int newPage) {
		if (newPage != getIndex()) {
			executeSaveOperation();
		}
	}

	public void executeSaveOperation() {
		final String newText = getCurrentContent();
		if (!oldText.equals(newText)) {
			final IFeatureModel fm = getFeatureModel();

			// TODO _interfaces replace text with DocumentEvent (delta)
			final SourceChangedOperation op = new SourceChangedOperation(fm, featureModelEditor, newText, oldText);

			op.addContext((IUndoContext) fm.getUndoContext());
			try {
				PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
				oldText = newText;
			} catch (final ExecutionException e) {
				FMUIPlugin.getDefault().logError(e);
			}
		}
	}

	@Override
	public void pageChangeTo(int oldPage) {
		if (oldPage != getIndex()) {
			if (featureModelEditor.isPageModified) {
				updateTextEditor();
			} else {
				resetTextEditor();
			}
			oldText = getDocumentProvider().getDocument(getEditorInput()).get();
		}
	}

	@Override
	public String getID() {
		return ID;
	}

	String getCurrentContent() {
		return getDocumentProvider().getDocument(getEditorInput()).get();
	}
}
