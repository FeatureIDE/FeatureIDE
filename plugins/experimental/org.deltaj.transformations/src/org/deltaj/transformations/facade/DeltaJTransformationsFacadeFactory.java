package org.deltaj.transformations.facade;

public class DeltaJTransformationsFacadeFactory {

	public static DeltaJTransformationsFacade create() {

		return new DeltaJTransformationsFacadeImpl();
	}
}
