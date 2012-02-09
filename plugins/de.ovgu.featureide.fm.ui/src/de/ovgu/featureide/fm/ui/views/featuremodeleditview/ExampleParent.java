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
package de.ovgu.featureide.fm.ui.views.featuremodeleditview;

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

	private ModelComparator c;

	private boolean added;

	private int number;

	private Configuration example;

	public ExampleParent(boolean added, ModelComparator c, int number, Configuration example) {
		super("next");
		this.added = added;
		this.c = c;
		this.number = number;
		this.example = example;

		if (number == 1)
			name = added ? "Added products" : "Removed products";
		if (c.getResult() == Comparison.ERROR) {
			image = IMAGE_UNDEFINED;
		} else {
			String imageName = added && !c.isImplied() ? "plus" : !added
					&& !c.isImplies() ? "minus" : "zero";
			lazy = !imageName.equals("zero");

			image = imageName.equals("plus") ? PLUS_IMAGE : imageName
					.equals("minus") ? MINUS_IMAGE : ZERO_IMAGE;
		}
	}

	@Override
	public void initChildren() {
		try {
			if (example == null) {
				example = c.calculateExample(added);
			}
			if (example == null) {
				addChild("none");
			}
			else {
				SelectableFeature root = example.getRoot();
				root.setName("Product " + number);
				addChild(root);
				
				Configuration example = c.calculateExample(added);
				if (example != null) {
					addChild(new ExampleParent(added, c, number + 1, example));
				}
			}
		} catch (TimeoutException e) {
			addChild("timeout");
		}
	}

}
