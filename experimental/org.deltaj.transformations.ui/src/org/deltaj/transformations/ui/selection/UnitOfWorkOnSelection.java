package org.deltaj.transformations.ui.selection;

import java.util.List;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.xtext.resource.XtextResource;
import org.eclipse.xtext.util.concurrent.IUnitOfWork;

public class UnitOfWorkOnSelection<R> implements IUnitOfWork<R, XtextResource> {

	private final DeltaJSelection selection;
	private final ISelectionHandler<R> selectionHandler;

	public UnitOfWorkOnSelection(DeltaJSelection selection, ISelectionHandler<R> selectionHandler) {

		this.selection = selection;
		this.selectionHandler = selectionHandler;
	}

	@Override
	public R exec(XtextResource resource) throws Exception {

		List<EObject> selectedObjects = selection.getSelectedObjects(resource);
		return selectionHandler.handle(selectedObjects);
	}
}
