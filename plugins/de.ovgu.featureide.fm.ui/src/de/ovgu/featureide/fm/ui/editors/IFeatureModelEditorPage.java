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

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;

/**
 * Basic interface for all pages at feature model editor.
 * 
 * @author Jens Meinicke
 */
public interface IFeatureModelEditorPage {

	/**
	 * 
	 * @return Identifier of this page.
	 */
	public String getID();
	
	/**
	 * @return the index of this page.
	 */
	public int getIndex();

	/**
	 * @param the index of this page.
	 */
	public void setIndex(int index);
	
	/**
	 * @return The Name of this page.
	 */
	public String getPageText();
	
	/**
	 * Called after adding the page to the editor. 
	 */
	public void initEditor();
	
	/**
	 * @param the feature model editor containing the page.
	 */
	public void setFeatureModelEditor(FeatureModelEditor featureModelEditor);
	
	/**
	 * @return This page. You can also call a constructor.
	 */
	public IFeatureModelEditorPage getPage(Composite container);

	/**
	 * 
	 * @return The control of this page.
	 */
	public Control getControl();

	/**
	 * @param monitor
	 */
	public void doSave(IProgressMonitor monitor);

	/**
	 * Called if the file has been changed.
	 * @param event
	 */
	public void propertyChange(PropertyChangeEvent event);

	/**
	 * Called if the tab has been changed from this page.
	 * @param newPage
	 */
	public void pageChangeFrom(int newPage);

	/**
	 * Called if the tab has been changed to this page.
	 * @param oldPage
	 */
	public void pageChangeTo(int oldPage);
}
