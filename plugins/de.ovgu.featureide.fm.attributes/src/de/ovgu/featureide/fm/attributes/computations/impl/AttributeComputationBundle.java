package de.ovgu.featureide.fm.attributes.computations.impl;

import java.util.ArrayList;
import java.util.List;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.computations.IAttributeComputation;
import de.ovgu.featureide.fm.core.configuration.Configuration;

/**
 * 
 * Creates a list with the computations used in the Attribute calculations outline
 * 
 * @author Chico Sundermann
 */
public class AttributeComputationBundle {

	List<IAttributeComputation> computations;

	public void initComputations(Configuration config, IFeatureAttribute attribute) {
		computations = new ArrayList<IAttributeComputation>();
		computations.add(new CountAttributeComputation(config, attribute));
		computations.add(new EstimatedMinimumComputation(config, attribute));
		computations.add(new EstimatedMaximumComputation(config, attribute));
	}

	public List<ComputationHeader> getComputationHeaders() {
		List<ComputationHeader> headers = new ArrayList<ComputationHeader>();
		for (IAttributeComputation comp : computations) {
			headers.add(new ComputationHeader(comp));
		}
		return headers;
	}

	private List<IAttributeComputation> getExtensions(Configuration config, IFeatureAttribute attribute) {
		List<IAttributeComputation> extensions = new ArrayList<IAttributeComputation>();
		return extensions;
	}
}
