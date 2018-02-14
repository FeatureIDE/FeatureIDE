package de.ovgu.featureide.fm.ui.views.outline.computations;

/**
 *
 * Holds an IAttribute computation
 *
 * @author Chico Sundermann
 */
public class ComputationHeader {

	IConfigurationComputation computation;

	public ComputationHeader(IConfigurationComputation computation) {
		this.computation = computation;
	}

	public String getName() {
		return computation.getHeaderString();
	}

	public IConfigurationComputation getComputation() {
		return computation;
	}
}
