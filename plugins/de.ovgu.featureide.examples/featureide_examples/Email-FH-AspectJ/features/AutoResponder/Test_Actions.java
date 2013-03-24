import java.util.ArrayList;
import java.util.List;

import EmailSystem.Client;
import EmailSystem.Util;
import TestSpecifications.SpecificationManager;

/**
 * This class implements the actions that can be executed by the test scenarios.
 * (setup() is always executed first to setup the characters and their private keys)
 * @author rhein
 */
public class Test_Actions {

	static void rjhSetAutoRespond() {
		actionHistory.add("rjhSetAutoRespond");
		rjh.setAutoResponse(true);
	}

}
