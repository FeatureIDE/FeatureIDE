package de.ovgu.featureide.core.builder;

import de.ovgu.featureide.core.IFeatureProject;

public interface IComposerExtension extends IComposerExtensionBase {
	
	public static String extensionPointID = "composers";
	
	public static String extensionID = "composer";
	
	IComposerExtensionClass getComposerByProject(IFeatureProject featureProject);

}
