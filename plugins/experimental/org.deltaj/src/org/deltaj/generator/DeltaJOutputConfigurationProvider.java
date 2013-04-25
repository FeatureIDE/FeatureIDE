/**
 * 
 */
package org.deltaj.generator;

import java.util.Set;

import org.eclipse.xtext.generator.OutputConfiguration;
import org.eclipse.xtext.generator.OutputConfigurationProvider;

/**
 * @author bettini
 * 
 */
public class DeltaJOutputConfigurationProvider extends
		OutputConfigurationProvider {

	@Override
	public Set<OutputConfiguration> getOutputConfigurations() {
		Set<OutputConfiguration> outputconfigurations = super
				.getOutputConfigurations();
		OutputConfiguration outputConfiguration = outputconfigurations
				.iterator().next();
		outputConfiguration
				.setOutputDirectory(DeltaJBuilder.DELTAJ_GEN_DIRECTORY);
		return outputconfigurations;
	}
}
