/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.core.search;

import java.io.File;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.core.fstmodel.FSTFeature;

/**
 * TODO description
 * 
 * @author franziskaheyden
 */
public class Result {
	
	private File file;
	private FSTFeature feature;
	private boolean isFile;
	private boolean isFeature;
	private IFile f;
	
	public Result(boolean isFile, boolean isFeature){
		this.isFeature = isFeature;
		this.isFile = isFile;
	}
	
	public void setFile(File f){
		if (isFile)
			file = f;
	}
	
	public File getFile(){
		return file;
	}

	/**
	 * @return the feature
	 */
	public FSTFeature getFeature() {
		return feature;
	}

	/**
	 * @param feature the feature to set
	 */
	public void setFeature(FSTFeature feature) {
		if (isFeature)	
			this.feature = feature;
	}

	/**
	 * @return the isFile
	 */
	public boolean isFile() {
		return isFile;
	}

	/**
	 * @return the isFeature
	 */
	public boolean isFeature() {
		return isFeature;
	}

	/**
	 * @return the f
	 */
	public IFile getIFile() {
		return f;
	}

	/**
	 * @param f the f to set
	 */
	public void setIFile(IFile f) {
		this.f = f;
	}
}
