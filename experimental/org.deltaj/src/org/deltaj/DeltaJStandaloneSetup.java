
package org.deltaj;

/**
 * Initialization support for running Xtext languages 
 * without equinox extension registry
 */
public class DeltaJStandaloneSetup extends DeltaJStandaloneSetupGenerated{

	public static void doSetup() {
		new DeltaJStandaloneSetup().createInjectorAndDoEMFRegistration();
	}
}

