package org.deltaj.transformations.ui.transformations;

import org.deltaj.deltaj.DeltaModule;
import org.deltaj.transformations.merge.DeltaJModulesWithInverseMerger;
import org.deltaj.transformations.ui.menu.IconEnum;
import org.deltaj.transformations.ui.transformation.AbstractTransformationCommandHandler;

class MergeDeltaModulesWithInverses extends AbstractTransformationCommandHandler {

	public MergeDeltaModulesWithInverses() {

		super(
				"Merge Delta Modules With Inverses",
				IconEnum.MERGE,
				"Merges two delta modules and creates inverse deltas to retain the behavior.");
	}

	void transform(DeltaModule deltaA, DeltaModule deltaB) {

		new DeltaJModulesWithInverseMerger(deltaA, deltaB).merge();
	}
}
