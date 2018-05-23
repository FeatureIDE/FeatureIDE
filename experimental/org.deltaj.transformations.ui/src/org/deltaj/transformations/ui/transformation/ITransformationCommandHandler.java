package org.deltaj.transformations.ui.transformation;

import java.util.List;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.jface.resource.ImageDescriptor;

public interface ITransformationCommandHandler {

	String getName();

	String getDescription();

	ImageDescriptor getIcon();

	void transform(List<EObject> selectedObjects);

	boolean isValidSelection(List<EObject> selectedObjects);
}
