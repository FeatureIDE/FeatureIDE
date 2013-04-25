package org.deltaj.transformations.modules.references;

import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.PartitionPart;
import org.deltaj.deltaj.DeltaPartition;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.deltaj.ProductLine;

public interface DeltaJModuleReference {

	ModuleReference getStatement();

	DeltaModule getDeltaModule();

	DeltaPartition getPartition();

	PartitionPart getPartitionPart();

	int getPartitionOrder();

	String getSplName();

	ProductLine getSplSpecification();

	PropositionalFormula getApplicationCondition();
}
