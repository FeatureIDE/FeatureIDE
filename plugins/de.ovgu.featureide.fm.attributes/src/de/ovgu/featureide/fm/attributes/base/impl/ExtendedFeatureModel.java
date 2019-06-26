package de.ovgu.featureide.fm.attributes.base.impl;

import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FeatureModel;

/**
 * Represents extended feature models. Extends the {@link FeatureModel} provided by FeatureIDE. Provides copy constructors and copy methods.
 * 
 * @author Joshua Sprey
 * @author Chico SUndermann
 */
public class ExtendedFeatureModel extends FeatureModel {

	IFeatureModelFactory factory;

	public ExtendedFeatureModel(ExtendedFeatureModel copyFeatureModel, ExtendedFeature newRoot) {
		super(copyFeatureModel, newRoot);

		try {
			factory = FMFactoryManager.getInstance().getFactory(factoryID);
		} catch (NoSuchExtensionException e) {
			factory = new ExtendedFeatureModelFactory();
		}
	}

	public ExtendedFeatureModel(String factoryID) {
		super(factoryID);

		try {
			factory = FMFactoryManager.getInstance().getFactory(factoryID);
		} catch (NoSuchExtensionException e) {
			factory = new ExtendedFeatureModelFactory();
		}
	}

	@Override
	public void createDefaultValues(CharSequence projectName) {
		String rootName = getValidJavaIdentifier(projectName);
		if (rootName.isEmpty()) {
			rootName = "Root";
		}
		if (featureTable.isEmpty()) {
			final IFeature root = factory.createFeature(this, rootName);
			structure.setRoot(root.getStructure());
			addFeature(root);
		}
		final IFeature feature = factory.createFeature(this, "Base");
		addFeature(feature);

		structure.getRoot().addChild(feature.getStructure());
		structure.getRoot().setAbstract(true);
	}

	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder();
		builder.append("ExtendedFeatureModel[");
		for (IFeature feature : getFeatures()) {
			builder.append(feature.toString() + ", ");
		}
		builder.append("]");
		return builder.toString();
	}

	@Override
	public FeatureModel clone() {
		return new ExtendedFeatureModel(this, null);
	}
}
