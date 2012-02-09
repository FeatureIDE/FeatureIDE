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

import org.eclipse.jface.fieldassist.TextContentAdapter;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Text;

/**
 * contentAdapter for content assist while typing constraints 
 * 
 * @author David Broneske
 * @author Fabian Benduhn
 */
public class ConstraintContentAdapter extends TextContentAdapter {
	public void insertControlContents(Control control, String text,
			int cursorPosition) {

		Point selection = ((Text) control).getSelection();
		String constraintText = ((Text) control).getText();

		int posMarker = selection.y - 1;
		if (cursorPosition != 0) {
			while (posMarker >= 0 && (constraintText.charAt(posMarker) != ' '&&constraintText.charAt(posMarker)!=')'&&constraintText.charAt(posMarker)!='(')) {

				posMarker--;
			}
		}
		selection.x = posMarker + 1;

		((Text) control).setSelection(selection);
		((Text) control).insert(text);

		// Insert will leave the cursor at the end of the inserted text. If this
		// is not what we wanted, reset the selection.
		if (cursorPosition < text.length()) {
			((Text) control).setSelection(selection.x + cursorPosition,
					selection.x + cursorPosition);
		}
	}
}
