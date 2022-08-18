/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.Iterator;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.texteditor.IDocumentProvider;

import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.SourceChangedOperation;

/**
 * Displays the source.
 *
 * @author Jens Meinicke
 * @author Marcus Pinnecke (Feature Interface)
 */
public class FeatureModelTextEditorPage extends TextEditor implements IFeatureModelEditorPage {

	public static final String ID = FMUIPlugin.PLUGIN_ID + ".editors.FeatureModelTextEditorPage";
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
		final FeatureModelManager manager = featureModelEditor.getFeatureModelManager();
		final String text = manager.processObject(manager.getFormat().getInstance()::write, FeatureModelManager.CHANGE_NOTHING);
		final IDocument document = getDocumentProvider().getDocument(getEditorInput());
		if (!document.get().equals(text)) {
			document.set(text);
		}
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
		try {
			internalSave(progressMonitor);
		} catch (final Exception e) {}
	}

	public void internalSave(IProgressMonitor progressMonitor) {
		final ProblemList problems = featureModelEditor.checkModel(getCurrentContent());
		if (problems.containsError()) {
			createMarkers(problems);
		} else {
			deleteMarkers(getDocumentProvider().getAnnotationModel(getEditorInput()));
		}
		super.doSave(progressMonitor);
		executeSaveOperation();
		featureModelEditor.setPageModified(false);
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
		if (newPage == getIndex()) {
			return true;
		}
		final ProblemList problems = featureModelEditor.checkModel(getCurrentContent());
		final boolean containsError = problems.containsError();
		if (containsError) {
			createMarkers(problems);
		} else {
			deleteMarkers(getDocumentProvider().getAnnotationModel(getEditorInput()));
		}
		return !containsError;
	}

	private void createMarkers(ProblemList problems) {
		final IDocumentProvider documentProvider = getDocumentProvider();
		final IEditorInput editorInput = getEditorInput();
		final IDocument document = documentProvider.getDocument(editorInput);
		final IAnnotationModel annotationModel = documentProvider.getAnnotationModel(editorInput);
		deleteMarkers(annotationModel);
		for (final Problem problem : problems) {
			final Annotation annotation = new Annotation(false);
			annotation.setText(problem.getMessage());
			switch (problem.getSeverity()) {
			case ERROR:
				annotation.setType("org.eclipse.ui.workbench.texteditor.error");
				break;
			case INFO:
				annotation.setType("org.eclipse.ui.workbench.texteditor.info");
				break;
			case WARNING:
				annotation.setType("org.eclipse.ui.workbench.texteditor.warning");
				break;
			}
			int lineOffset = 0;
			try {
				lineOffset = document.getLineOffset(problem.getLine());
			} catch (final BadLocationException e) {}
			annotationModel.addAnnotation(annotation, new Position(lineOffset));
		}
	}

	private void deleteMarkers(final IAnnotationModel annotationModel) {
		for (final Iterator<Annotation> iterator = annotationModel.getAnnotationIterator(); iterator.hasNext();) {
			annotationModel.removeAnnotation(iterator.next());
		}
	}

	@Override
	public void pageChangeFrom(int newPage) {
		if (newPage != getIndex()) {
			executeSaveOperation();
		}
	}

	@Override
	protected void createUndoRedoActions() {}

	public void executeSaveOperation() {
		final String newText = getCurrentContent();
		if (!oldText.equals(newText)) {
			// TODO _interfaces replace text with DocumentEvent (delta)
			if (FeatureModelOperationWrapper.run(new SourceChangedOperation(featureModelEditor.fmManager, newText, oldText))) {
				oldText = newText;
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
