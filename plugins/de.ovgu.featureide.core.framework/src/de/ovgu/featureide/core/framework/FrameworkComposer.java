package de.ovgu.featureide.core.framework;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.core.builder.ComposerExtensionClass;

/**
 * TODO fill in
 * 
 * @author Daniel Hohmann
 *
 */
public class FrameworkComposer extends ComposerExtensionClass {

	@Override
	public Mechanism getGenerationMechanism() {
		return null;
	}

	@Override
	public void performFullBuild(IFile config) {
	//TODO Update .classpath
	}
	
}
