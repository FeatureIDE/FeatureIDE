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
package de.ovgu.featureide.core.fstmodel;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;

/**
 * Represents arbitrary files.
 *
 * @author Jens Meinicke
 */
public class FSTArbitraryRole extends FSTRole {

	private final List<IFile> files = new LinkedList<IFile>();

	/**
	 * @param file
	 * @param feature
	 * @param fstClass
	 */
	public FSTArbitraryRole(FSTFeature feature, FSTClass fstClass) {
		super(null, feature, fstClass);
	}

	void addFile(final IFile file) {
		if (!files.contains(file)) {
			files.add(file);
		}
	}

	/**
	 * @return the files
	 */
	public List<IFile> getFiles() {
		return Collections.unmodifiableList(files);
	}

}
