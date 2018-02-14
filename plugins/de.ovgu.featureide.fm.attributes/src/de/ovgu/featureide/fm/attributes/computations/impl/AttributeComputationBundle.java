package de.ovgu.featureide.fm.attributes.computations.impl;

import java.util.ArrayList;
import java.util.List;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.ui.views.outline.computations.ComputationHeader;
import de.ovgu.featureide.fm.ui.views.outline.computations.IConfigurationComputation;

/**
 * 
 * Creates a list with the computations used in the Attribute calculations outline
 * 
 * @author Chico Sundermann
 */
public class AttributeComputationBundle {

	List<IConfigurationComputation> computations;

	public void initComputations(Configuration config, IFeatureAttribute attribute) {
		computations = new ArrayList<IConfigurationComputation>();
		computations.add(new CountAttributeComputation(config, attribute));
		computations.add(new EstimatedMinimumComputation(config, attribute));
		computations.add(new EstimatedMaximumComputation(config, attribute));
	}

	public List<ComputationHeader> getComputationHeaders() {
		List<ComputationHeader> headers = new ArrayList<ComputationHeader>();
		for (IConfigurationComputation comp : computations) {
			headers.add(new ComputationHeader(comp));
		}
		return headers;
	}

	private List<IConfigurationComputation> getExtensions(Configuration config, IFeatureAttribute attribute) {
		List<IConfigurationComputation> extensions = new ArrayList<IConfigurationComputation>();
		return extensions;
	}
}
