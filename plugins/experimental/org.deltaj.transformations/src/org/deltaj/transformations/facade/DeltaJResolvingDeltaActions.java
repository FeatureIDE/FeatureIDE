package org.deltaj.transformations.facade;

import org.deltaj.deltaj.ClassRemoval;
import org.deltaj.deltaj.DeltaAction;
import org.deltaj.deltaj.FieldRemoval;
import org.deltaj.deltaj.MethodModification;
import org.deltaj.deltaj.MethodRemoval;
import org.deltaj.deltaj.ProductLine;

public interface DeltaJResolvingDeltaActions {

	void resolveDuplicatedAction(DeltaAction deltaActionA, DeltaAction deltaActionB);

	void resolveMethodModificationAction(MethodModification methodModification);

	void resolveMethodModificationActions(ProductLine productLine);

	void resolveRemovalAction(ClassRemoval classRemoval);

	void resolveRemovalAction(MethodRemoval methodRemoval);

	void resolveRemovalAction(FieldRemoval fieldRemoval);

	void resolveRemovalActions(ProductLine productLine);
}
