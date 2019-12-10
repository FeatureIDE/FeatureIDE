package de.ovgu.featureide.fm.attributes.computations.impl;

import de.ovgu.featureide.fm.attributes.computations.IAttributeComputation;

public class ComputationHeader {

	IAttributeComputation computation;

	public ComputationHeader(IAttributeComputation computation) {
		this.computation = computation;
	}

	public String getName() {
		return computation.getHeaderString();
	}

	public IAttributeComputation getAttributeComputation() {
		return computation;
	}
}
