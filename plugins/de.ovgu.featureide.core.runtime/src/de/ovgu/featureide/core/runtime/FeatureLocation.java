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
package de.ovgu.featureide.core.runtime;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirectiveCommand;

/**
 * Class for objects containing necessary information of feature locations within the code.
 *
 * @author Kai Wolf
 * @author Matthias Quaas
 *
 */
class FeatureLocation {

	String featureName;
	int startLineNum;
	int endLineNum;
	IFile classFile;
	String className;
	FeatureLocation parent;
	boolean inConfig;
	FSTDirectiveCommand cmd;

	FeatureLocation(final String featureName, final int startLineNum, final int endLineNum, final IFile classFile, final String className,
			final FSTDirectiveCommand cmd) {
		this.featureName = featureName;
		this.startLineNum = startLineNum;
		this.endLineNum = endLineNum;
		this.classFile = classFile;
		this.className = className;
		parent = null;
		inConfig = false;
		this.cmd = cmd;
	}

	public IFile getClassFile() {
		return classFile;
	}

	public String getClassName() {
		return className;
	}

	public FSTDirectiveCommand getCmd() {
		return cmd;
	}

	public int getEndLineNum() {
		return endLineNum;
	}

	public String getFeatureName() {
		return featureName;
	}

	public String getOSPath() {
		return classFile.getFullPath().toOSString();
	}

	public FeatureLocation getParent() {
		return parent;
	}

	public int getStartLineNum() {
		return startLineNum;
	}

	public boolean isInConfig() {
		return inConfig;
	}

	public void setCmd(final FSTDirectiveCommand cmd) {
		this.cmd = cmd;
	}

	public void setFeatureName(final String featureName) {
		this.featureName = featureName;
	}

	public void setInConfig(final boolean inConfig) {
		this.inConfig = inConfig;
	}

	public void setParent(final FeatureLocation parent) {
		this.parent = parent;
	}

	@Override
	public String toString() {
		return getOSPath() + "_" + startLineNum + "_" + featureName;
	}

}
