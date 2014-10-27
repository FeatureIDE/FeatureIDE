package de.ovgu.featureide.core.builder;

import de.ovgu.featureide.core.IFeatureProject;

public interface IComposerExtension extends IComposerExtensionBase {
	
	IComposerExtensionClass getComposerByProject(IFeatureProject featureProject);
}
