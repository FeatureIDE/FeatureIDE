package org.deltaj.transformations.ui.selection;

import java.util.List;
import org.eclipse.emf.ecore.EObject;

public interface ISelectionHandler<R> {

	R handle(List<EObject> selectedObjects);
}
