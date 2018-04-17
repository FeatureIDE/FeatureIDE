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
package de.ovgu.featureide.ui.editors.annotation;

import static de.ovgu.featureide.fm.core.localization.StringTable.BLUE;
import static de.ovgu.featureide.fm.core.localization.StringTable.COLOR_ANNOTATION;
import static de.ovgu.featureide.fm.core.localization.StringTable.CYAN;
import static de.ovgu.featureide.fm.core.localization.StringTable.DARKGREEN;
import static de.ovgu.featureide.fm.core.localization.StringTable.LIGHTGREEN;
import static de.ovgu.featureide.fm.core.localization.StringTable.LIGHTGREY;
import static de.ovgu.featureide.fm.core.localization.StringTable.MARGENTA;
import static de.ovgu.featureide.fm.core.localization.StringTable.ORANGE;
import static de.ovgu.featureide.fm.core.localization.StringTable.PINK;
import static de.ovgu.featureide.fm.core.localization.StringTable.RED;
import static de.ovgu.featureide.fm.core.localization.StringTable.YELLOW;

import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.Annotation;

/**
 * One class for all color annotations
 *
 * @author Sebastian Krieter
 */
public class ColorAnnotation extends Annotation {

	public static final int TYPE_IMAGE = 0;
	public static final int TYPE_HIGHLIGHT_OVERVIEW = 1;
	public static final int TYPE_HIGHLIGHT = 2;
	public static final int TYPE_OVERVIEW = 3;

	private static final String[] ANNOTATIONTYPE_ID = new String[31];
	static {
		final String PREFIX = "de.ovgu.featureide.ui.editors.annotations.";
		final String[] COLORS = { RED, ORANGE, YELLOW, DARKGREEN, LIGHTGREEN, CYAN, LIGHTGREY, BLUE, MARGENTA, PINK };
		ANNOTATIONTYPE_ID[0] = PREFIX + "image";

		for (int i = 0; i < (ANNOTATIONTYPE_ID.length - 1); i++) {
			ANNOTATIONTYPE_ID[i + 1] = PREFIX + COLORS[i % COLORS.length] + ((i / COLORS.length) + 1);
		}
	}

	private final Position position;
	private final int id;
	private final int type;

	public ColorAnnotation(int id, Position posistion, int annotationtype) {
		super(getTypeString(id, annotationtype), false, COLOR_ANNOTATION);
		position = posistion;
		this.id = id;
		type = annotationtype;
	}

	private static String getTypeString(int id, int type) {
		if (id == -1) {
			return "de.ovgu.featureide.ui.editors.annotations.image";
		}
		switch (type) {
		case TYPE_IMAGE:
			return ANNOTATIONTYPE_ID[0];
		case TYPE_HIGHLIGHT_OVERVIEW:
			return ANNOTATIONTYPE_ID[id + 1];
		case TYPE_HIGHLIGHT:
			return ANNOTATIONTYPE_ID[id + 11];
		case TYPE_OVERVIEW:
			return ANNOTATIONTYPE_ID[id + 21];
		default:
			return null;
		}
	}

	public Position getPosition() {
		return position;
	}

	public void updateOffset(int deltaOffset) {
		position.offset += deltaOffset;
	}

	public void updateLength(int deltaLength) {
		position.length += deltaLength;
	}

	public String getId() {
		return Integer.toString(id);
	}

	public boolean isImageAnnotation() {
		return (type == TYPE_IMAGE) && (id != -1);
	}
}
