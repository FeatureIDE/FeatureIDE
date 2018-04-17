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

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorPart;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.io.manager.IFileManager;

/**
 * Basic class with some default methods for feature model editor pages.
 *
 * @author Jens Meinicke
 * @author Sebastian Krieter
 */
public abstract class FeatureModelEditorPage extends EditorPart implements IFeatureModelEditorPage {

	protected final IFileManager<IFeatureModel> fmManager;

	private int index;

	protected IEditorInput input;
	protected IEditorSite site;

	public FeatureModelEditorPage(IFileManager<IFeatureModel> fmManager) {
		super();
		this.fmManager = fmManager;
	}

	public IFeatureModel getFeatureModel() {
		return fmManager.editObject();
	}

	@Override
	public void doSave(IProgressMonitor monitor) {
		setDirty(false);
	}

	@Override
	public void doSaveAs() {}

	@Override
	public void init(IEditorSite site, IEditorInput input) throws PartInitException {
		this.input = input;
		this.site = site;
	}

	@Override
	public boolean isDirty() {
		return false;
	}

	protected void setDirty(boolean dirty) {
		firePropertyChange(PROP_DIRTY);
	}

	@Override
	public boolean isSaveAsAllowed() {
		return false;
	}

	@Override
	public void createPartControl(Composite parent) {}

	@Override
	public void setFocus() {}

	@Override
	public int getIndex() {
		return index;
	}

	@Override
	public void setIndex(int index) {
		this.index = index;
	}

	@Override
	public IEditorSite getSite() {
		return site;
	}

	@Override
	public void initEditor() {}

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
		return true;
	}

	@Override
	public void pageChangeFrom(int newPage) {}

	@Override
	public void pageChangeTo(int oldPage) {}

}
