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

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.fieldassist.IContentProposal;

/**
 * Copy of org.eclipse.jface.fieldassist.ContentProposal included in eclipse 3.6
 * 
 * @author Fabian Benduhn
 */
public class ContentProposal implements IContentProposal {
	private static final String EMPTY = ""; //$NON-NLS-1$

	private String content = EMPTY;
	private String label = EMPTY;
	private String description = EMPTY;
	private int cursorPosition = 0;

	/**
	 * Create a content proposal whose label and content are the specified
	 * String. The cursor position will be located at the end of the content.
	 * 
	 * @param content
	 *            the String representing the content. Should not be
	 *            <code>null</code>.
	 */
	public ContentProposal(String content) {
		this(content, content, null);
	}

	/**
	 * Create a content proposal whose content and description are as specified
	 * in the parameters. The cursor position will be located at the end of the
	 * content.
	 * 
	 * @param content
	 *            the String representing the content. Should not be
	 *            <code>null</code>. This string will also be used as the label.
	 * @param description
	 *            the String representing the description, or <code>null</code>
	 *            if there should be no description.
	 */
	public ContentProposal(String content, String description) {
		this(content, content, description);
	}

	/**
	 * Create a content proposal whose content, label, and description are as
	 * specified in the parameters. The cursor position will be located at the
	 * end of the content.
	 * 
	 * @param content
	 *            the String representing the content. Should not be
	 *            <code>null</code>.
	 * @param label
	 *            the String representing the label. Should not be
	 *            <code>null</code>.
	 * 
	 * @param description
	 *            the String representing the description, or <code>null</code>
	 *            if there should be no description.
	 */
	public ContentProposal(String content, String label, String description) {
		this(content, label, description, content.length());
	}

	/**
	 * Create a content proposal whose content, label, description, and cursor
	 * position are as specified in the parameters.
	 * 
	 * @param content
	 *            the String representing the content. Should not be
	 *            <code>null</code>.
	 * @param label
	 *            the String representing the label. Should not be
	 *            <code>null</code>.
	 * 
	 * @param description
	 *            the String representing the description, or <code>null</code>
	 *            if there should be no description.
	 * 
	 * @param cursorPosition
	 *            the zero-based index position within the contents where the
	 *            cursor should be placed after the proposal is accepted. The
	 *            range of the cursor position is from 0..N where N is the
	 *            number of characters in the content.
	 * 
	 * @exception IllegalArgumentException
	 *                if the index is not between 0 and the number of characters
	 *                in the content.
	 */
	public ContentProposal(String content, String label, String description,
			int cursorPosition) {
		Assert.isNotNull(content);
		Assert.isNotNull(label);
		Assert.isLegal(cursorPosition >= 0
				&& cursorPosition <= content.length());
		this.content = content;
		this.label = label;
		this.description = description;
		this.cursorPosition = cursorPosition;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.fieldassist.IContentProposal#getContent()
	 */
	public String getContent() {
		return content;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.fieldassist.IContentProposal#getCursorPosition()
	 */
	public int getCursorPosition() {
		return cursorPosition;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.fieldassist.IContentProposal#getDescription()
	 */
	public String getDescription() {
		return description;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.fieldassist.IContentProposal#getLabel()
	 */
	public String getLabel() {
		return label;
	}

	public String toString() {
		return content + "-" + label;
	}
}