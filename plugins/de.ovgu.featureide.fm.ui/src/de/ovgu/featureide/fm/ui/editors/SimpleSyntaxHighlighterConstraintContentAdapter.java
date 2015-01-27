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

import org.eclipse.jface.fieldassist.IControlContentAdapter;
import org.eclipse.jface.fieldassist.IControlContentAdapter2;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.widgets.Control;

/**
 * contentAdapter for content assist while typing constraints
 * 
 * @author David Broneske
 * @author Fabian Benduhn
 */
public class SimpleSyntaxHighlighterConstraintContentAdapter implements IControlContentAdapter, IControlContentAdapter2 {
	
	public void insertControlContents(Control control, String text, int cursorPosition) {
		Point selection = ((SimpleSyntaxHighlightEditor) control).getSelection();
		int posMarker = selection.y - 1;
		if (cursorPosition != 0) {
			String constraintText = ((SimpleSyntaxHighlightEditor) control).getText();
			while (posMarker >= 0 && (constraintText.charAt(posMarker) != ' ' && constraintText.charAt(posMarker) != ')' && constraintText.charAt(posMarker) != '(')) {
				posMarker--;
			}
		}
		selection.x = posMarker + 1;

		((SimpleSyntaxHighlightEditor) control).setSelection(selection);
		((SimpleSyntaxHighlightEditor) control).insert(text);

		// Insert will leave the cursor at the end of the inserted text. If this
		// is not what we wanted, reset the selection.
		if (cursorPosition < text.length()) {
			((SimpleSyntaxHighlightEditor) control).setSelection(selection.x + cursorPosition, selection.x + cursorPosition);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.dialogs.taskassistance.IControlContentAdapter#
	 * getControlContents(org.eclipse.swt.widgets.Control)
	 */
	public String getControlContents(Control control) {
		return ((SimpleSyntaxHighlightEditor) control).getText();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.jface.fieldassist.IControlContentAdapter#setControlContents
	 * (org.eclipse.swt.widgets.Control, java.lang.String, int)
	 */
	public void setControlContents(Control control, String text, int cursorPosition) {
		((SimpleSyntaxHighlightEditor) control).setText(text);
		((SimpleSyntaxHighlightEditor) control).setSelection(cursorPosition, cursorPosition);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.jface.fieldassist.IControlContentAdapter#getCursorPosition
	 * (org.eclipse.swt.widgets.Control)
	 */
	public int getCursorPosition(Control control) {
		return ((SimpleSyntaxHighlightEditor) control).getSelectionRanges()[0];
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.jface.fieldassist.IControlContentAdapter#getInsertionBounds
	 * (org.eclipse.swt.widgets.Control)
	 */
	public Rectangle getInsertionBounds(Control control) {
		SimpleSyntaxHighlightEditor text = (SimpleSyntaxHighlightEditor) control;
		Point caretOrigin = text.getSelection();
		// We fudge the y pixels due to problems with getCaretLocation
		// See https://bugs.eclipse.org/bugs/show_bug.cgi?id=52520
		return new Rectangle(caretOrigin.x + text.getClientArea().x, caretOrigin.y + text.getClientArea().y + 3, 1, text.getLineHeight());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.jface.fieldassist.IControlContentAdapter#setCursorPosition
	 * (org.eclipse.swt.widgets.Control, int)
	 */
	public void setCursorPosition(Control control, int position) {
		((SimpleSyntaxHighlightEditor) control).setSelection(new Point(position, position));
	}

	/**
	 * @see org.eclipse.jface.fieldassist.IControlContentAdapter2#getSelection(org.eclipse.swt.widgets.Control)
	 * 
	 * @since 3.4
	 */
	public Point getSelection(Control control) {
		return ((SimpleSyntaxHighlightEditor) control).getSelection();
	}

	/**
	 * @see org.eclipse.jface.fieldassist.IControlContentAdapter2#setSelection(org.eclipse.swt.widgets.Control,
	 *      org.eclipse.swt.graphics.Point)
	 * 
	 * @since 3.4
	 */
	public void setSelection(Control control, Point range) {
		((SimpleSyntaxHighlightEditor) control).setSelection(range);
	}
}
