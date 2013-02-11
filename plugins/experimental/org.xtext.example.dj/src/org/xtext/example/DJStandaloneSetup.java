
package org.xtext.example;

import org.xtext.example.DJStandaloneSetupGenerated;

/**
 * Initialization support for running Xtext languages 
 * without equinox extension registry
 */
public class DJStandaloneSetup extends DJStandaloneSetupGenerated{

	public static void doSetup() {
		new DJStandaloneSetup().createInjectorAndDoEMFRegistration();
	}
}

