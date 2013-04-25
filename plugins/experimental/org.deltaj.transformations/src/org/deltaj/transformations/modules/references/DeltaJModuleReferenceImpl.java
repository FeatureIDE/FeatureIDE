package org.deltaj.transformations.modules.references;

import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.PartitionPart;
import org.deltaj.deltaj.DeltaPartition;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.transformations.utils.ListUtils;
import org.deltaj.transformations.utils.exceptions.DeltaJException;

public class DeltaJModuleReferenceImpl implements DeltaJModuleReference {

	private final ModuleReference referenceStatement;
	private final int partitionOrder;

	private DeltaJModuleReferenceImpl(ModuleReference referenceStatement, int partitionOrder) {

		this.referenceStatement = referenceStatement;
		this.partitionOrder = partitionOrder;
	}

	public static DeltaJModuleReference get(ModuleReference referenceStatement, int partitionOrder) {

		return new DeltaJModuleReferenceImpl(referenceStatement, partitionOrder);
	}

	public static DeltaJModuleReference get(ModuleReference moduleReference) {

		int partitionOrder = getPartitionOrder(moduleReference);

		return new DeltaJModuleReferenceImpl(moduleReference, partitionOrder);
	}

	private static int getPartitionOrder(ModuleReference moduleReference) {

		PartitionPart partitionPart = (PartitionPart) moduleReference.eContainer();
		int partitionOrder = ListUtils.findElementByIdentity(partitionPart.getModuleReferences(), moduleReference);

		if (partitionOrder < 0) {
			throw new DeltaJException("Failed to find partition order of module reference.");
		}

		return partitionOrder;
	}

	@Override
	public ModuleReference getStatement() {

		return referenceStatement;
	}

	@Override
	public DeltaModule getDeltaModule() {

		return getStatement().getDeltaModule();
	}

	@Override
	public PartitionPart getPartitionPart() {

		return (PartitionPart) getStatement().eContainer();
	}

	@Override
	public DeltaPartition getPartition() {

		return (DeltaPartition) getPartitionPart().eContainer();
	}

	@Override
	public ProductLine getSplSpecification() {

		return (ProductLine) getPartition().eContainer();
	}

	@Override
	public int getPartitionOrder() {

		return partitionOrder;
	}

	@Override
	public String getSplName() {

		return getSplSpecification().getName();
	}

	@Override
	public PropositionalFormula getApplicationCondition() {

		return getStatement().getWhen();
	}
}
