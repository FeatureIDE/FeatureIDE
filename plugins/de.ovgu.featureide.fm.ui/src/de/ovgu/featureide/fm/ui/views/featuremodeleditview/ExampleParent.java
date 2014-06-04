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
			lazy = !"zero".equals(imageName);

			image = "plus".equals(imageName) ? PLUS_IMAGE : "minus"
					.equals(imageName) ? MINUS_IMAGE : ZERO_IMAGE;
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
