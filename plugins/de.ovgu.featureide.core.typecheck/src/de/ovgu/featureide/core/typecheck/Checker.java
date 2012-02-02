package de.ovgu.featureide.core.typecheck;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.Feature;

public class Checker {

	IFeatureProject project;
	FujiWrapper wrap;

	public Checker(IFeatureProject project) {
		this.project = project;
		this.wrap = new FujiWrapper();
	}

	public void run() {

		String sourcePath = project.getSourcePath();
		Collection<Feature> features = project.getFeatureModel().getConcreteFeatures();
		List<String> concrete_features = new ArrayList<String>();

		for (Feature feature : features) {
			concrete_features.add(feature.getName());
		}

		if (project.getFeatureModel().isFeatureOrderUserDefined()) {
			wrap.getAST(sourcePath, project.getFeatureModel()
					.getFeatureOrderList());
		} else {
			wrap.getAST(sourcePath, concrete_features);
		}

	}
}
