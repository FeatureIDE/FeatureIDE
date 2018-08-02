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
package de.ovgu.featureide.fm.core.analysis.mig;

/**
 * Convenience methods for handling a {@link ModalImplicationGraph}.
 *
 * @author Sebastian Krieter
 */
public class MIGUtils {

	private MIGUtils() {}

	public static boolean isStronglyConnected(ModalImplicationGraph modalImplicationGraph, int startVariable, int endVariable) {
		final int[] strongEdges = modalImplicationGraph.getVertex(startVariable).getStrongEdges();
		for (int i = 0; i < strongEdges.length; i++) {
			if (strongEdges[i] == endVariable) {
				return true;
			}
		}
		return false;
	}

	public static int[] getStronglyConnected(ModalImplicationGraph modalImplicationGraph, int startVariable) {
		return modalImplicationGraph.getVertex(startVariable).getStrongEdges();
	}
}
