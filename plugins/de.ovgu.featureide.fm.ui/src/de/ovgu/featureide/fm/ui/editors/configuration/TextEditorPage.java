/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.editors.configuration;

import java.beans.PropertyChangeEvent;

import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.texteditor.IDocumentProvider;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.configuration.ConfigurationReader;
import de.ovgu.featureide.fm.core.configuration.ConfigurationWriter;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Displays the source.
 * 
 * @author Jens Meinicke
 */
public class TextEditorPage extends TextEditor implements IConfigurationEditorPage {

	private static final String ID = FMUIPlugin.PLUGIN_ID + "TextEditorPage";
	private static final String PAGE_TEXT = "Source";

	private int index;

	private IConfigurationEditor configurationEditor;

	@Override
	public String getID() {
		return ID;
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
	public void setConfigurationEditor(IConfigurationEditor configurationEditor) {
		this.configurationEditor = configurationEditor;
	}

	@Override
	public String getPageText() {
		return PAGE_TEXT;
	}

	@Override
	public void propertyChange(PropertyChangeEvent evt) {
		refresh();
	}

	protected final void refresh() {
		if (configurationEditor.getConfiguration() == null) {
			return;
		}
		String source = new ConfigurationWriter(configurationEditor.getConfiguration()).writeIntoString();
		IDocumentProvider provider = getDocumentProvider();
		IDocument document = provider.getDocument(getEditorInput());
		if (!source.equals(document.get())) {
			document.set(source);
		}
	}

	@Override
	public void pageChangeFrom(int newPageIndex) {
		IDocumentProvider provider = getDocumentProvider();
		IDocument document = provider.getDocument(getEditorInput());
		String text = document.get();
		if (!new ConfigurationWriter(configurationEditor.getConfiguration()).writeIntoString().equals(text)) {
			try {
				new ConfigurationReader(configurationEditor.getConfiguration()).readFromString(text);
			} catch (Exception e) {
				FMCorePlugin.getDefault().logError(e);
			}
		}
	}

	@Override
	public void pageChangeTo(int oldPageIndex) {
		refresh();
	}

	@Override
	public IConfigurationEditorPage getPage() {
		return this;
	}

}
