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
package de.ovgu.featureide.fm.ui.editors.configuration;

import java.beans.PropertyChangeEvent;

import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.texteditor.IDocumentProvider;

import de.ovgu.featureide.fm.core.configuration.ConfigurationWriter;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Displays the source.
 * 
 * @author Jens Meinicke
 */
public class TextEditorPage extends TextEditor implements IConfigurationEditorPage{

	private static final String ID = FMUIPlugin.PLUGIN_ID + "TextEditorPage";
	private static final String PAGE_TEXT = "Source";

	private int index;

	private ConfigurationEditor configurationEditor;
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.editors.IConfigurationEditorPage#getID()
	 */
	@Override
	public String getID() {
		return ID;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.editors.IConfigurationEditorPage#getIndex()
	 */
	@Override
	public int getIndex() {
		return index;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.editors.IConfigurationEditorPage#setIndex(int)
	 */
	@Override
	public void setIndex(int index) {
		this.index = index;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.editors.IConfigurationEditorPage#setConfigurationEditor(de.ovgu.featureide.ui.editors.ConfigurationEditor)
	 */
	@Override
	public void setConfigurationEditor(ConfigurationEditor configurationEditor) {
		this.configurationEditor = configurationEditor;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.editors.IConfigurationEditorPage#getPageText()
	 */
	@Override
	public String getPageText() {
		return PAGE_TEXT;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.editors.IConfigurationEditorPage#propertyChange(java.beans.PropertyChangeEvent)
	 */
	@Override
	public void propertyChange(PropertyChangeEvent evt) {
		if(configurationEditor.configuration==null){
	
			return;
		}
		String source = new ConfigurationWriter(configurationEditor.configuration)
				.writeIntoString(configurationEditor.file);
		IDocumentProvider provider = getDocumentProvider();
		IDocument document = provider
				.getDocument(getEditorInput());
		if (!source.equals(document.get()))
			document.set(source);
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.editors.IConfigurationEditorPage#pageChangeFrom(int)
	 */
	@Override
	public void pageChangeFrom(int index) {
	
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.editors.IConfigurationEditorPage#pageChangeTo(int)
	 */
	@Override
	public void pageChangeTo(int index) {

	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.editors.IConfigurationEditorPage#getPage()
	 */
	@Override
	public IConfigurationEditorPage getPage() {
		return this;
	}
	
}
