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

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorPart;



/**
 * Basic class with some default methods for configuration editor pages.
 * 
 * @author Jens Meinicke
 */
public abstract class ConfigurationEditorPage extends EditorPart implements IConfigurationEditorPage {

	protected ConfigurationEditor configurationEditor = null;
	
	private int index;
	
	protected boolean dirty;
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.editors.IConfigurationEditorPage#setIndex(int)
	 */
	@Override
	public void setIndex(int index) {
		this.index = index;
	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.editors.IConfigurationEditorPage#getIndex()
	 */
	@Override
	public int getIndex() {
		return index;
	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.editors.IConfigurationEditorPage#setConfigurationEditor(de.ovgu.featureide.ui.editors.ConfigurationEditor)
	 */
	@Override
	public void setConfigurationEditor(ConfigurationEditor configurationEditor) {
		this.configurationEditor = configurationEditor;
	}
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.editors.IConfigurationEditorPage#propertyChange(java.beans.PropertyChangeEvent)
	 */
	@Override
	public void propertyChange(PropertyChangeEvent evt) {
	
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
	 * @see org.eclipse.ui.part.EditorPart#doSave(org.eclipse.core.runtime.IProgressMonitor)
	 */
	@Override
	public void doSave(IProgressMonitor monitor) {
		dirty = false;
		firePropertyChange(IEditorPart.PROP_DIRTY);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.part.EditorPart#doSaveAs()
	 */
	@Override
	public void doSaveAs() {
		
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.part.EditorPart#init(org.eclipse.ui.IEditorSite, org.eclipse.ui.IEditorInput)
	 */
	@Override
	public void init(IEditorSite site, IEditorInput input)
			throws PartInitException {
		setSite(site);
		setInput(input);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.part.EditorPart#isDirty()
	 */
	@Override
	public boolean isDirty() {
		return dirty;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.part.EditorPart#isSaveAsAllowed()
	 */
	@Override
	public boolean isSaveAsAllowed() {
		return false;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.part.WorkbenchPart#createPartControl(org.eclipse.swt.widgets.Composite)
	 */
	@Override
	public void createPartControl(Composite parent) {
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.part.WorkbenchPart#setFocus()
	 */
	@Override
	public void setFocus() {
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.editors.IConfigurationEditorPage#getPage()
	 */
	@Override
	public IConfigurationEditorPage getPage() {
		return this;
	}
}
