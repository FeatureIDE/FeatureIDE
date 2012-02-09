package de.ovgu.featureide.core.typecheck;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.typecheck.parser.Parser;
import de.ovgu.featureide.fm.core.Feature;

public class Checker {

	IFeatureProject _project;
	Parser _parser;

	public Checker(IFeatureProject project) {
		_project = project;
		_parser = new Parser();
	}

	public void run() {

		String sourcePath = _project.getSourcePath();
		Collection<Feature> features = _project.getFeatureModel().getConcreteFeatures();
		List<String> concrete_features = new ArrayList<String>();

		for (Feature feature : features) {
			concrete_features.add(feature.getName());
		}

		if (_project.getFeatureModel().isFeatureOrderUserDefined()) {
			_parser.parse(sourcePath, _project.getFeatureModel()
					.getFeatureOrderList());
		} else {
			_parser.parse(sourcePath, concrete_features);
		}
		System.out.println(_parser.getClassTable().dumpString());
	}
}
