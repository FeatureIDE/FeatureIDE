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
package de.ovgu.featureide.fm.ui.views.featuremodeleditview;

import static de.ovgu.featureide.fm.core.localization.StringTable.ADDED_PRODUCTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.MINUS;
import static de.ovgu.featureide.fm.core.localization.StringTable.NEXT;
import static de.ovgu.featureide.fm.core.localization.StringTable.NONE;
import static de.ovgu.featureide.fm.core.localization.StringTable.PLUS;
import static de.ovgu.featureide.fm.core.localization.StringTable.PRODUCT;
import static de.ovgu.featureide.fm.core.localization.StringTable.REMOVED_PRODUCTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.TIMEOUT_STRING;
import static de.ovgu.featureide.fm.core.localization.StringTable.ZERO;

import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.editing.Comparison;
import de.ovgu.featureide.fm.core.editing.ModelComparator;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * Calculates an example for added or removed products.
 *
 * @author Thomas Thuem
 */
public class ExampleParent extends TreeParent implements GUIDefaults {

	private final ModelComparator c;

	private final boolean added;

	private final int number;

	private Configuration example;

	public ExampleParent(boolean added, ModelComparator c, int number, Configuration example) {
		super(NEXT);
		this.added = added;
		this.c = c;
		this.number = number;
		this.example = example;

		if (number == 1) {
			name = added ? ADDED_PRODUCTS : REMOVED_PRODUCTS;
		}
		if (c.getResult() == Comparison.ERROR) {
			image = IMAGE_UNDEFINED;
		} else {
			final String imageName = added && !c.isImplied() ? PLUS : !added && !c.isImplies() ? MINUS : ZERO;
			lazy = !ZERO.equals(imageName);

			image = PLUS.equals(imageName) ? PLUS_IMAGE : MINUS.equals(imageName) ? MINUS_IMAGE : ZERO_IMAGE;
		}
	}

	@Override
	public void initChildren() {
		try {
			if (example == null) {
				example = c.calculateExample(added);
			}
			if (example == null) {
				addChild(NONE);
			} else {
				final SelectableFeature root = example.getRoot();
				root.setName(PRODUCT + number);
				addChild(root);

				final Configuration example = c.calculateExample(added);
				if (example != null) {
					addChild(new ExampleParent(added, c, number + 1, example));
				}
			}
		} catch (final TimeoutException e) {
			addChild(TIMEOUT_STRING);
		}
	}

}
