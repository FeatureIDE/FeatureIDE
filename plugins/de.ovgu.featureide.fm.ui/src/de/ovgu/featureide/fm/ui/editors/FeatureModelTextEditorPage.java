/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors;

import java.beans.PropertyChangeEvent;

import org.eclipse.core.resources.IMarker;
import org.eclipse.jface.text.IDocument;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.editors.text.TextEditor;
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
public class FeatureModelTextEditorPage extends TextEditor implements
		IFeatureModelEditorPage {

	private int index;
	
	private static final String PAGE_TEXT = "Source";

	private static final String ID = FMUIPlugin.PLUGIN_ID + ".editors.FeatureModelTextEditorPage";
	
	private FeatureModelEditor featureModelEditor;

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IFeatureModelEdiorPage#getIndex()
	 */
	@Override
	public int getIndex() {
		return index;
	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IFeatureModelEditorPage#setIndex(int)
	 */
	@Override
	public void setIndex(int index) {
		this.index = index;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IFeatureModelEditorPage#getPageText()
	 */
	@Override
	public String getPageText() {
		return PAGE_TEXT;
	}

	/**
	 * Updates the text editor from diagram.
	 */
	public void updateTextEditor() {
		String text = featureModelEditor.featureModelWriter.writeToString();
		getDocumentProvider().getDocument(getEditorInput()).set(text);
	}
	
	/**
	 * Updates the diagram from text editor.
	 * @return false if the text is not supported.
	 */
	public boolean updateDiagram() {
		IDocumentProvider provider = getDocumentProvider();
		IDocument document = provider.getDocument(getEditorInput());
		String text = document.get();
		featureModelEditor.fmFile.deleteAllModelMarkers();
		try {
			featureModelEditor.featureModelReader.readFromString(text);
			for (ModelWarning warning : featureModelEditor.featureModelReader.getWarnings())
				featureModelEditor.fmFile.createModelMarker(warning.message,
						IMarker.SEVERITY_WARNING, warning.line);
			try {
				if (!featureModelEditor.featureModel.getAnalyser().isValid())
					featureModelEditor.fmFile.createModelMarker(
							"The feature model is void, i.e., it contains no products",
							IMarker.SEVERITY_ERROR, 0);
			} catch (TimeoutException e) {
				// do nothing, assume the model is correct
			}
		} catch (UnsupportedModelException e) {
			featureModelEditor.fmFile.createModelMarker(e.getMessage(), IMarker.SEVERITY_ERROR,
					e.lineNumber);
			return false;
		}
		return true;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IFeatureModelEditorPage#initEditor()
	 */
	@Override
	public void initEditor() {
		
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IFeatureModelEditorPage#setFeatureModelEditor(de.ovgu.featureide.fm.ui.editors.FeatureModelEditor)
	 */
	@Override
	public void setFeatureModelEditor(FeatureModelEditor featureModelEditor) {
		this.featureModelEditor = featureModelEditor;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IFeatureModelEditorPage#getPage()
	 */
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
			
		if (featureModelEditor.featureModel.isRenamed()) {
			featureModelEditor.saveModelForConsistentRenamings();
		}
	}

	@Override
	public String getID() {
		return ID;
	}

}
