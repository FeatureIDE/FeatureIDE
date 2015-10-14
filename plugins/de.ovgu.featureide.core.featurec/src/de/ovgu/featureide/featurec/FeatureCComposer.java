package de.ovgu.featureide.featurec;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.featurehouse.FeatureHouseComposer;

public class FeatureCComposer extends ComposerExtensionClass {

	private FeatureHouseComposer composer;
	
	public FeatureCComposer() {
		composer = new FeatureHouseComposer();
	}

	@Override
	public void performFullBuild(IFile config) {
		composer.performFullBuild(config);
	}

	@Override
	public Mechanism getGenerationMechanism() {
		return composer.getGenerationMechanism();
	}

}
