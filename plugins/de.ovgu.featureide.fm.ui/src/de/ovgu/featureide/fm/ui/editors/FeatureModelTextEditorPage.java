/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors;

import java.beans.PropertyChangeEvent;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.io.ModelWarning;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Displays the source.
 * 
 * @author Jens Meinicke
 */
public class FeatureModelTextEditorPage extends TextEditor implements IFeatureModelEditorPage {

	private int index;

	private static final String PAGE_TEXT = "Source";

	private static final String ID = FMUIPlugin.PLUGIN_ID
			+ ".editors.FeatureModelTextEditorPage";

	private FeatureModelEditor featureModelEditor;
	
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
	public void updateTextEditor() {
		// prevent writing incorrectly read models due to errors in the model
		if (featureModelEditor.fmFile.hasModelMarkers())
			return;
		String text = featureModelEditor.featureModelWriter.writeToString();
		getDocumentProvider().getDocument(getEditorInput()).set(text);
	}

	/**
	 * Reads the current content of the model.xml file.
	 * (Removes dirty state for the page)
	 */
	public void resetTextEditor() {
		try {
			getDocumentProvider().resetDocument(getEditorInput());
		} catch (CoreException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

	/**
	 * Updates the diagram from text editor.
	 * 
	 * @return false if the text is not supported.
	 */
	public boolean updateDiagram() {
		IDocumentProvider provider = getDocumentProvider();
		IDocument document = provider.getDocument(getEditorInput());
		String text = document.get();
		featureModelEditor.fmFile.deleteAllModelMarkers();
		try {
			IEditorInput input = getEditorInput();
			if (input instanceof FileEditorInput) {
				IFile file = ((FileEditorInput) input).getFile();
				featureModelEditor.featureModelReader.setFile(file
						.getLocation().toFile());
			}

			featureModelEditor.featureModelReader.readFromString(text);
			for (ModelWarning warning : featureModelEditor.featureModelReader
					.getWarnings())
				featureModelEditor.fmFile.createModelMarker(warning.message,
						IMarker.SEVERITY_WARNING, warning.line);
			try {
				if (!featureModelEditor.featureModel.getAnalyser().isValid())
					featureModelEditor.fmFile
							.createModelMarker(
									"The feature model is void, i.e., it contains no products",
									IMarker.SEVERITY_ERROR, 0);
			} catch (TimeoutException e) {
				// do nothing, assume the model is correct
			}
		} catch (UnsupportedModelException e) {
			featureModelEditor.fmFile.createModelMarker(e.getMessage(),
					IMarker.SEVERITY_ERROR, e.lineNumber);
			return false;
		}
		return true;
	}
	
	@Override
	public void initEditor() {

	}
	
	@Override
	public void setFeatureModelEditor(FeatureModelEditor featureModelEditor) {
		this.featureModelEditor = featureModelEditor;
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
	public void propertyChange(PropertyChangeEvent event) {

	}

	@Override
	public void pageChangeFrom(int newPage) {

	}

	@Override
	public void pageChangeTo(int oldPage) {
		if (featureModelEditor.isPageModified) {
			updateTextEditor();
		}

		if (featureModelEditor.featureModel.getRenamingsManager().isRenamed()) {
			featureModelEditor.saveModelForConsistentRenamings();
		}
	}

	@Override
	public String getID() {
		return ID;
	}

}
