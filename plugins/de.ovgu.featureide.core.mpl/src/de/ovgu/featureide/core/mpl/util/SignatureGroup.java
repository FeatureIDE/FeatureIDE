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
package de.ovgu.featureide.core.mpl.util;

import org.eclipse.core.resources.IFolder;

public class SignatureGroup implements Comparable<SignatureGroup> {

	private final int id;
	private final IFolder folder;
	private int size = 0;

	public SignatureGroup(int id, IFolder folder) {
		this.id = id;
		this.folder = folder;
	}

	public void addSig() {
		size++;
	}

	@Override
	public int compareTo(SignatureGroup otherSigGroup) {
		final int dSize = size - otherSigGroup.size;
		return dSize != 0 ? dSize : otherSigGroup.id - id;
	}

	public IFolder getFolder() {
		return folder;
	}

	public int getId() {
		return id;
	}

	public int size() {
		return size;
	}
}
