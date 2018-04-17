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
package de.ovgu.featureide.fm.ui.editors.configuration;

import static de.ovgu.featureide.fm.core.localization.StringTable.SOURCE;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.editors.text.TextEditor;

import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Displays the source.
 *
 * @author Jens Meinicke
 */
public class TextEditorPage extends TextEditor implements IConfigurationEditorPage {

	public static final String ID = FMUIPlugin.PLUGIN_ID + "TextEditorPage";
	private static final String PAGE_TEXT = SOURCE;

	private int index;

	private ConfigurationEditor configurationEditor;

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
		this.configurationEditor = (ConfigurationEditor) configurationEditor;
	}

	@Override
	public String getPageText() {
		return PAGE_TEXT;
	}

	@Override
	public void propertyChange(FeatureIDEEvent evt) {
		if (evt != null) {
			switch (evt.getEventType()) {
			case MODEL_DATA_SAVED:
				try {
					getDocumentProvider().resetDocument(getEditorInput());
				} catch (final CoreException e) {
					e.printStackTrace();
				}
				break;
			default:
				break;
			}
		} else {
			refresh();
		}
	}

	protected final void refresh() {
		final ConfigurationManager configurationManager = configurationEditor.getConfigurationManager();
		if ((configurationManager != null) && (configurationEditor.getConfiguration() != null) && !configurationEditor.containsError()) {
			final String source = configurationManager.getFormat().getInstance().write(configurationEditor.getConfiguration());
			final IDocument document = getDocumentProvider().getDocument(getEditorInput());
			if (!source.equals(document.get())) {
				document.set(source);
			}
		}
	}

	@Override
	public void pageChangeFrom(int newPageIndex) {
		updateConfiguration();
	}

	public void updateConfiguration() {
		final String text = getDocumentProvider().getDocument(getEditorInput()).get();
		final IPersistentFormat<Configuration> confFormat = configurationEditor.getConfigurationManager().getFormat();
		if (!confFormat.getInstance().write(configurationEditor.getConfiguration()).equals(text)) {
			confFormat.getInstance().read(configurationEditor.getConfiguration(), text);
		}
		configurationEditor.loadPropagator();
	}

	@Override
	public void pageChangeTo(int oldPageIndex) {
		refresh();
	}

	@Override
	public IConfigurationEditorPage getPage() {
		return this;
	}

	@Override
	protected void editorSaved() {
		super.editorSaved();
		checkSource();
	}

	@Override
	public boolean allowPageChange(int newPageIndex) {
		final ProblemList problems = checkSource();
		return !(problems.containsError() || (isDirty() && problems.containsWarning()));
	}

	protected ProblemList checkSource() {
		final ConfigurationManager configurationManager = configurationEditor.getConfigurationManager();
		if (configurationManager != null) {
			final Configuration configuration = configurationEditor.getConfiguration();
			final IPersistentFormat<Configuration> confFormat = configurationManager.getFormat();

			final ProblemList problems = confFormat.getInstance().read(configuration, getDocumentProvider().getDocument(getEditorInput()).get());
			configurationEditor.createModelFileMarkers(problems);
			configurationEditor.setContainsError(problems.containsError());

			return problems;
		}
		return null;
	}

}
