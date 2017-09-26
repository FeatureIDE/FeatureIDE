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
package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import java.util.LinkedList;

import de.ovgu.featureide.core.fstmodel.FSTInvariant;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * Node for {@link FSTInvariant}.
 *
 * @author Schleicher Miro
 */
public class InvariantNodeParent extends Parent {

	private final FSTInvariant fstInvariant;

	public InvariantNodeParent(String discription, FSTInvariant fstInvariant, LinkedList<FSTInvariant> allInvariants) {
		super(discription);
		this.fstInvariant = fstInvariant;
		final int numberOfInvariants = countInvariantsWithSameName(allInvariants);
		setValue(new Integer(numberOfInvariants));
	}

	private int countInvariantsWithSameName(LinkedList<FSTInvariant> invariants) {
		int c = 0;
		for (final FSTInvariant tempInvariant : invariants) {
			if (tempInvariant.getRole().getClassFragment().getFullIdentifier().equals(fstInvariant.getRole().getClassFragment().getFullIdentifier())) {
				c++;

				addChild(new Parent(tempInvariant.getRole().getFeature().getName(), tempInvariant));
			}
		}
		return c;
	}

	public FSTInvariant getInvariant() {
		return fstInvariant;
	}
}
