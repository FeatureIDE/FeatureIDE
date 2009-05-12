/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
package featureide.fm.ui.views.featuremodeleditview;

import org.sat4j.specs.TimeoutException;

import featureide.fm.core.configuration.Configuration;
import featureide.fm.core.configuration.SelectableFeature;
import featureide.fm.core.editing.ModelComparator;
import featureide.fm.ui.FMUIPlugin;

/**
 * Calculates an example for added or removed products.
 * 
 * @author Thomas Thuem
 */
public class ExampleParent extends TreeParent {

	private ModelComparator c;
	
	private boolean added;

	private int number;

	public ExampleParent(boolean added, ModelComparator c, int number) {
		super("next");
		this.added = added;
		this.c = c;
		this.number = number;
		if (number == 1)
			name = added ? "Added products" : "Removed products";
		String imageName = added && !c.isImplied() ? "plus" : !added
				&& !c.isImplies() ? "minus" : "zero";
		lazy = !imageName.equals("zero");
		if (number > 1)
	 		image = FMUIPlugin.getImage("undefined.ico");
		else
			image = FMUIPlugin.getImage(imageName + ".gif");
	}

	@Override
	public void initChildren() {
		try {
			Configuration example = c.calculateExample(added);
			if (example == null)
				addChild("none");
			else {
				SelectableFeature root = example.getRoot();
				root.setName("Product " + number);
				addChild(root);
				addChild(new ExampleParent(added, c, number + 1));
			}
		} catch (TimeoutException e) {
			addChild("timeout");
		}
	}

}
