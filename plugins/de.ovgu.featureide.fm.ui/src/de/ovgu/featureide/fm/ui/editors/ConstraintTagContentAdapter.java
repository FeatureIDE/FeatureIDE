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

import org.eclipse.jface.fieldassist.IControlContentAdapter;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.widgets.Control;

/**
 * ContentAdapter for content assist while typing constraint tags
 *
 * @author Rahel Arens
 */
public class ConstraintTagContentAdapter implements IControlContentAdapter {

	@Override
	public void insertControlContents(Control control, String contents, int cursorPosition) {
		((StyledText) control).setText(contents);
	}

	@Override
	public void setControlContents(Control control, String contents, int cursorPosition) {
		((StyledText) control).setText(contents);
	}

	@Override
	public String getControlContents(Control control) {
		return ((StyledText) control).getText();
	}

	@Override
	public int getCursorPosition(Control control) {
		return ((StyledText) control).getText().length();
	}

	@Override
	public Rectangle getInsertionBounds(Control control) {
		final StyledText text = (StyledText) control;
		final Point caretOrigin = text.getSelection();

		return new Rectangle(caretOrigin.x + text.getClientArea().x, caretOrigin.y + text.getClientArea().y + 3, 1, text.getLineHeight());
	}

	@Override
	public void setCursorPosition(Control control, int index) {
		((StyledText) control).setSelection(new Point(index, index));
	}

}
