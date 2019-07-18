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

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.IPropertyListener;
import org.eclipse.ui.IWorkbenchPartSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.FileEditorInput;

import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.configuration.IConfigurationEditor;
import de.ovgu.featureide.fm.ui.editors.configuration.IConfigurationEditorPage;

/**
 * Displays a simple error message.
 *
 * @author Sebastian Krieter
 */
public class ConfigurationEditorErrorPage implements IConfigurationEditorPage {

	public static final String ID = FMUIPlugin.PLUGIN_ID + ".editors.ConfigurationEditorErrorPage";

	private static final String PAGE_TEXT = "Error";

	private IEditorSite site;

	@Override
	public void createPartControl(Composite parent) {
		final Composite composite = new Composite(parent, SWT.NONE);
		final RowLayout layout = new RowLayout(SWT.HORIZONTAL);
		layout.marginLeft = 10;
		layout.marginTop = 10;
		layout.spacing = 8;
		composite.setLayout(layout);
		final Label imageLabel = new Label(composite, SWT.NONE);
		imageLabel.setImage(FMUIPlugin.getImage("fmerror.png"));
		final Label textLabel = new Label(composite, SWT.NONE);
		final IEditorInput editorInput = getEditorInput();
		if (editorInput instanceof FileEditorInput) {
			textLabel.setText("File <" + editorInput.getName() + "> does not appear to be a configuration!");
		} else {
			textLabel.setText("Input does not appear to be a configuration!");
		}
	}

	@Override
	public String getPageText() {
		return PAGE_TEXT;
	}

	@Override
	public String getID() {
		return ID;
	}

	@Override
	public IEditorInput getEditorInput() {
		return null;
	}

	@Override
	public IEditorSite getEditorSite() {
		return null;
	}

	@Override
	public void init(IEditorSite site, IEditorInput input) throws PartInitException {
		this.site = site;
	}

	@Override
	public void addPropertyListener(IPropertyListener listener) {}

	@Override
	public void dispose() {}

	@Override
	public IWorkbenchPartSite getSite() {
		return site;
	}

	@Override
	public String getTitle() {
		return PAGE_TEXT;
	}

	@Override
	public Image getTitleImage() {
		return FMUIPlugin.getImage("fmerror.png");
	}

	@Override
	public String getTitleToolTip() {
		return "";
	}

	@Override
	public void removePropertyListener(IPropertyListener listener) {}

	@Override
	public void setFocus() {}

	@Override
	public <T> T getAdapter(Class<T> adapter) {
		return null;
	}

	@Override
	public void doSave(IProgressMonitor monitor) {}

	@Override
	public void doSaveAs() {}

	@Override
	public boolean isDirty() {
		return false;
	}

	@Override
	public boolean isSaveAsAllowed() {
		return false;
	}

	@Override
	public boolean isSaveOnCloseNeeded() {
		return false;
	}

	@Override
	public void propertyChange(FeatureIDEEvent event) {}

	@Override
	public int getIndex() {
		return 0;
	}

	@Override
	public void setIndex(int index) {}

	@Override
	public void setConfigurationEditor(IConfigurationEditor configurationEditor) {}

	@Override
	public void pageChangeFrom(int newPageIndex) {}

	@Override
	public void pageChangeTo(int oldPageIndex) {}

	@Override
	public IConfigurationEditorPage getPage() {
		return this;
	}

	@Override
	public boolean allowPageChange(int newPageIndex) {
		return false;
	}

}
