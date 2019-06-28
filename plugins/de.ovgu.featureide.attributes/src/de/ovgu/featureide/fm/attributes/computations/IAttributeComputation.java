package de.ovgu.featureide.fm.attributes.computations;

import de.ovgu.featureide.fm.core.configuration.Configuration;

/**
 * 
 * Interface, that a computation used in the Attribute calculation should implement
 * 
 * @author Chico Sundermann
 */
public interface IAttributeComputation {

	public Object[] getResult();

	public String getResultString();

	public Configuration getConfiguration();

	public String getHeaderString();
}
