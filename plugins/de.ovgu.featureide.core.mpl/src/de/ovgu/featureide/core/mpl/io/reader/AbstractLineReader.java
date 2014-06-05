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
package de.ovgu.featureide.core.mpl.io.reader;

import java.io.BufferedReader;
import java.io.InputStreamReader;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.core.mpl.MPLPlugin;

/**
 * Reads a file line by line and returns the results. 
 * 
 * @author Sebastian Krieter
 */
public abstract class AbstractLineReader<E> {
	protected E infoObj = null;
	protected IFile file;
	
	public AbstractLineReader(IFile file) {
		this.file = file;
	}
	
	public AbstractLineReader() {
		this.file = null;
	}

	protected abstract boolean prepareRead();
	protected abstract boolean readLine(String line);

	public IFile getFile() {
		return file;
	}

	public void setFile(IFile file) {
		this.file = file;
	}
	
	public E read() {
		if (file != null) {
			try {
				BufferedReader br = new BufferedReader(new InputStreamReader(file.getContents()));
				if (prepareRead()) {
					String line = null;
					while ((line = br.readLine()) != null) {
						if (!readLine(line)) {
							return null;
						}
					}
					return infoObj;
				}
			} catch (Exception e) {
				MPLPlugin.getDefault().logError(e);
			}
		}
		return null;
	}
}
