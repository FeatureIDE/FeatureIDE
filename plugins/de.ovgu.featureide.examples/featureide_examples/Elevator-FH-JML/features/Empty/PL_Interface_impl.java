import TestSpecifications.SpecificationManager;

import ElevatorSystem.Elevator;
import ElevatorSystem.Environment;
import ElevatorSystem.Person;
import java.util.List;
import java.util.ArrayList;
import java.lang.Throwable;

public class PL_Interface_impl {

	// this method is used as hook for the liveness properties.
	/*@
	  @ ensures \original;
	  @ ensures (\forall int i; 0 <= i && i < env.calledAt_Spec9.length; !env.calledAt_Spec9[i]);
	  @*/
	public void test(int specification, int variation) {
		original(specification, variation);
	}

}
