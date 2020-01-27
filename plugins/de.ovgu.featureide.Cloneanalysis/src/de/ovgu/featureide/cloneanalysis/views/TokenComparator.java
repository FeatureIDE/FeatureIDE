/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.cloneanalysis.views;

import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerComparator;

import de.ovgu.featureide.cloneanalysis.impl.CloneOccurence;
import de.ovgu.featureide.cloneanalysis.results.Clone;

public class TokenComparator extends ViewerComparator {

	boolean sortDescending;

	public TokenComparator(boolean sortDescending) {
		this.sortDescending = sortDescending;
	}

	@Override
	public int compare(Viewer viewer, Object e1, Object e2) {
		int t1 = 0, t2 = 0, result = 0;
		if (e1 instanceof Clone) t1 = ((Clone) e1).getTokenCount();
		else if (e1 instanceof CloneOccurence) t1 = ((CloneOccurence) e1).getClone().getTokenCount();
		if (e2 instanceof Clone) t2 = ((Clone) e2).getTokenCount();
		else if (e2 instanceof CloneOccurence) t2 = ((CloneOccurence) e2).getClone().getTokenCount();

		if (sortDescending == true) {
			result = t2 - t1;
		} else {
			result = t1 - t2;
		}

		return result;
	}
}
