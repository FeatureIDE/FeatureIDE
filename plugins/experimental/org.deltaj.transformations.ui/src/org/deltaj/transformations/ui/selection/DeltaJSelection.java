package org.deltaj.transformations.ui.selection;

import java.util.Collections;
import java.util.List;
import org.deltaj.transformations.utils.ListFactory;
import org.deltaj.transformations.utils.exceptions.DeltaJException;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.xtext.resource.XtextResource;
import org.eclipse.xtext.ui.editor.outline.impl.EObjectNode;

/**
 * Represents a selection of a {@link EObject} list.
 * 
 * @author Oliver Richers
 */
public class DeltaJSelection {

	private final List<String> uriFragments;

	public static DeltaJSelection create(Object selection) {

		if (selection instanceof IStructuredSelection) {
			return new DeltaJSelection((IStructuredSelection) selection);
		} else {
			System.err.printf("Ignoring selection of type %s\n", selection.getClass().getCanonicalName());
			return new DeltaJSelection();
		}
	}

	private DeltaJSelection(IStructuredSelection selection) {

		this.uriFragments = ListFactory.createArrayList();

		for (Object selectedElement: selection.toList()) {
			if (selectedElement instanceof EObjectNode) {
				EObjectNode objectNode = (EObjectNode) selectedElement;
				String uriFragment = objectNode.getEObjectURI().fragment();
				uriFragments.add(uriFragment);
			} else if (selectedElement == null) {
				throw new DeltaJException("The selected element is null but should be an EObjectNode.");
			} else {
				System.err.printf("Ignoring selected element because it is not an EObjectNode: %s\n", selectedElement
						.getClass()
						.getCanonicalName());
			}
		}
	}

	public DeltaJSelection() {

		this.uriFragments = Collections.emptyList();
	}

	public List<EObject> getSelectedObjects(XtextResource resource) {

		List<EObject> selectedObjects = ListFactory.createArrayList();

		for (String uriFragment: uriFragments) {
			EObject object = getEObject(resource, uriFragment);
			selectedObjects.add(object);
		}

		return selectedObjects;
	}

	private EObject getEObject(XtextResource resource, String uriFragment) {

		EObject object = resource.getEObject(uriFragment);

		if (object == null) {
			throw new DeltaJException("Failed to find matching EObject for URI fragment '%s'.", uriFragment);
		}

		return object;
	}
}
