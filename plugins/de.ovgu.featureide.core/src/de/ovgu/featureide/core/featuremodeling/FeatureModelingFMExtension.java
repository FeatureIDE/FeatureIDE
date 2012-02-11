package de.ovgu.featureide.core.featuremodeling;

import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.fm.core.FMComposerExtension;

/**
 * FMComposerExtension for the Feature Modeling extension.
 * 
 * @author Jens Meinicke
 */
public class FeatureModelingFMExtension extends FMComposerExtension {

	public FeatureModelingFMExtension() {
		
	}

	@Override
	public boolean isValidFeatureName(String s) {
		return true;
	}
	
	@Override
	public boolean performRenaming(String oldName, String newName,
			IProject project) {
		return true;
	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.FMComposerExtension#hasFeaureOrder()
	 */
	@Override
	public boolean hasFeaureOrder() {
		return false;
	}
}
