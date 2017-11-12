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
import org.eclipse.ui.IEditorPart;

import de.ovgu.featureide.fm.core.base.event.IEventListener;

/**
 * Basic interface for all pages at feature model editor.
 *
 * @author Jens Meinicke
 */
public interface IFeatureModelEditorPage extends IEditorPart, IEventListener {

	/**
	 *
	 * @return Identifier of this page.
	 */
	String getID();

	/**
	 * @return the index of this page.
	 */
	int getIndex();

	/**
	 * @param the index of this page.
	 */
	void setIndex(int index);

	/**
	 * @return The Name of this page.
	 */
	String getPageText();

	/**
	 * Called after adding the page to the editor.
	 */
	void initEditor();

	/**
	 * @return This page. You can also call a constructor.
	 */
	IFeatureModelEditorPage getPage(Composite container);

	/**
	 *
	 * @return The control of this page.
	 */
	Control getControl();

	/**
	 * @param monitor
	 */
	@Override
	void doSave(IProgressMonitor monitor);

	/**
	 * Called if this page is about to change to another page.
	 *
	 * @param newPage
	 *
	 * @return {@code true} if the user is allowed to change the page
	 */
	boolean allowPageChange(int newPage);

	/**
	 * Called if the tab has been changed from this page.
	 *
	 * @param newPage
	 */
	void pageChangeFrom(int newPage);

	/**
	 * Called if the tab has been changed to this page.
	 *
	 * @param oldPage
	 */
	void pageChangeTo(int oldPage);
}
