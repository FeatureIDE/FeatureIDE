package de.ovgu.featureide.fm.ui.views.outline.computations;

import de.ovgu.featureide.fm.core.configuration.Configuration;

/**
 *
 * Interface, that a computation used in the Attribute calculation should implement
 *
 * @author Chico Sundermann
 */
public interface IConfigurationComputation {

	public Object[] getResult();

	public String getResultString();

	public Configuration getConfiguration();

	public String getHeaderString();

	public boolean supportsType(Object element);
}
