package org.deltaj.transformations.facade;

import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.Product;
import org.deltaj.deltaj.ProductLine;

public interface DeltaJRenamingEntities {

	void renameDeltaModule(DeltaModule deltaModule, String newName);

	void renameFeature(Feature feature, String newName);

	void renameProduct(Product product, String newName);

	void renameProductLine(ProductLine productLine, String newName);
}
