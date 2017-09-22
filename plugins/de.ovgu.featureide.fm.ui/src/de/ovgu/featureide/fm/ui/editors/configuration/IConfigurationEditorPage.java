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

import org.eclipse.ui.IEditorPart;

import de.ovgu.featureide.fm.core.base.event.IEventListener;

/**
 * Basic interface for all pages at configuration editor.
 *
 * @author Jens Meinicke
 */
public interface IConfigurationEditorPage extends IEditorPart, IEventListener {

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
	 * @param the configuration editor containing the page.
	 */
	public void setConfigurationEditor(IConfigurationEditor configurationEditor);

	/**
	 * @return The Name of this page.
	 */
	public String getPageText();

	/**
	 * Called if the tab has been changed from this page.
	 *
	 * @param index of the new page
	 */
	public void pageChangeFrom(int newPageIndex);

	/**
	 * Called if the tab has been changed to this page.
	 *
	 * @param index of the old page
	 */
	public void pageChangeTo(int oldPageIndex);

	/**
	 * @return This page. You can also call a constructor.
	 */
	public IConfigurationEditorPage getPage();

	/**
	 * Called if this page is about to change to another page.
	 *
	 * @param newPageIndex
	 *
	 * @return {@code true} if the user is allowed to change the page
	 */
	public boolean allowPageChange(int newPageIndex);
}
