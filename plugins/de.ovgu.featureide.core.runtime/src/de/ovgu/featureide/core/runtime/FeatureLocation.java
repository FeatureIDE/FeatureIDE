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

	FeatureLocation(String featureName, int startLineNum, int endLineNum, IFile classFile, String className,
			FSTDirectiveCommand cmd) {
		this.featureName = featureName;
		this.startLineNum = startLineNum;
		this.endLineNum = endLineNum;
		this.classFile = classFile;
		this.className = className;
		this.parent = null;
		this.inConfig = false;
		this.cmd = cmd;
	}

	public FSTDirectiveCommand getCmd() {
		return cmd;
	}

	public String getFeatureName() {
		return featureName;
	}

	public int getStartLineNum() {
		return startLineNum;
	}

	public IFile getClassFile() {
		return classFile;
	}

	public String getClassName() {
		return className;
	}

	public int getEndLineNum() {
		return endLineNum;
	}

	public String getOSPath() {
		return classFile.getFullPath().toOSString();
	}

	public FeatureLocation getParent() {
		return parent;
	}

	public boolean isInConfig() {
		return inConfig;
	}

	public void setFeatureName(String featureName) {
		this.featureName = featureName;
	}

	public void setParent(FeatureLocation parent) {
		this.parent = parent;
	}

	public void setInConfig(boolean inConfig) {
		this.inConfig = inConfig;
	}

	public void setCmd(FSTDirectiveCommand cmd) {
		this.cmd = cmd;
	}

	public String toString() {
		return this.getOSPath() + "_" + startLineNum + "_" + featureName;
	}

}