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

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorPart;

/**
 * Basic class with some default methods for feature model editor pages.
 * 
 * @author Jens Meinicke
 */
public abstract class FeatureModelEditorPage extends EditorPart implements IFeatureModelEditorPage{

	private int index;
	
	protected FeatureModelEditor featureModelEditor;
	
	protected boolean dirty = false;
	
	protected IEditorInput input;

	protected IEditorSite site;
	
	/**
	 * @param featureModelEditor the featureModelEditor to set
	 */
	public void setFeatureModelEditor(FeatureModelEditor featureModelEditor) {
		this.featureModelEditor = featureModelEditor;
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
		this.input = input;
		this.site = site; 
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
	 * @see de.ovgu.featureide.fm.ui.editors.IFeatureModelEditorPage#getIndex()
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
	
	public IEditorSite getSite() {
		return site;
	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IFeatureModelEditorPage#initEditor()
	 */
	@Override
	public void initEditor() {
	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IFeatureModelEditorPage#getPage()
	 */
	@Override
	public IFeatureModelEditorPage getPage(Composite container) {
		return this;
	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IFeatureModelEditorPage#getControl1()
	 */
	@Override
	public Control getControl() {
		return null;
	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IFeatureModelEditorPage#propertyChange(java.beans.PropertyChangeEvent)
	 */
	@Override
	public void propertyChange(PropertyChangeEvent event) {
		
	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IFeatureModelEditorPage#pageChangeFrom(int)
	 */
	@Override
	public void pageChangeFrom(int newPage) {

	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IFeatureModelEditorPage#pageChangeTo(int)
	 */
	@Override
	public void pageChangeTo(int oldPage) {
	
	}
}
