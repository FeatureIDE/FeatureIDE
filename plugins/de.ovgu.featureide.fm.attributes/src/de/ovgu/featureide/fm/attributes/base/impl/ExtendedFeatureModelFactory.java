package de.ovgu.featureide.fm.attributes.base.impl;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.Constraint;

/**
 * 
 * Implementation of the {@link IFeatureModelFactory}. Creates extended feature models and extended features instead of the default ones.
 * 
 * @see IFeatureModelFactory
 * 
 * @author Joshua Sprey
 * @author Chico SUndermann
 */
public class ExtendedFeatureModelFactory implements IFeatureModelFactory {

	public static final String ID = "de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModelFactory";

	public static ExtendedFeatureModelFactory getInstance() {
		return new ExtendedFeatureModelFactory();
	}

	public ExtendedFeatureModelFactory() {}

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public boolean initExtension() {
		return true;
	}

	@Override
	public Constraint createConstraint(IFeatureModel featureModel, Node propNode) {
		return new Constraint(featureModel, propNode);
	}

	@Override
	public ExtendedFeature createFeature(IFeatureModel featureModel, String name) {
		return new ExtendedFeature(featureModel, name);
	}

	@Override
	public ExtendedFeatureModel create() {
		return new ExtendedFeatureModel(ID);
	}

	@Override
	public ExtendedFeature copyFeature(IFeatureModel featureModel, IFeature oldFeature) {
		return (ExtendedFeature) oldFeature.clone(featureModel, oldFeature.getStructure().clone(featureModel));
	}

	@Override
	public Constraint copyConstraint(IFeatureModel featureModel, IConstraint oldConstraint) {
		return (Constraint) oldConstraint.clone(featureModel);
	}

}
