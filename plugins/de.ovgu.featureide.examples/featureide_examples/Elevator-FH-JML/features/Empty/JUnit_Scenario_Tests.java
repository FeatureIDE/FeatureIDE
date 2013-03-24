import org.junit.Before; 
import org.junit.Test; 

import ElevatorSystem.Elevator; 
import ElevatorSystem.Environment; 
import ElevatorSystem.Person; 
import TestSpecifications.SpecificationException; 
import TestSpecifications.SpecificationManager; 

public  class  JUnit_Scenario_Tests {
	
	/**
	 * Hook for specifications with liveness properties. (indicator for
	 * test-termination)
	 */
	/*@
	  @ ensures \original;
	  @ ensures (\forall int i; 0 <= i && i < env.calledAt_Spec9.length; !env.calledAt_Spec9[i]);
	  @*/
	public void testFinished(Environment env) {
		original(env);
	}

}
