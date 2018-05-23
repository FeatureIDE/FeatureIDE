package org.deltaj.transformations.ui.transformation;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.List;
import org.deltaj.transformations.ui.menu.IconEnum;
import org.deltaj.transformations.ui.utils.ReflectionUtils;
import org.deltaj.transformations.utils.exceptions.DeltaJException;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.jface.resource.ImageDescriptor;

public abstract class AbstractTransformationCommandHandler implements ITransformationCommandHandler {

	private final String name;
	private final IconEnum icon;
	private final String description;

	public AbstractTransformationCommandHandler(String name, IconEnum icon, String description) {

		this.name = name;
		this.icon = icon;
		this.description = description;
	}

	@Override
	public String getName() {

		return name;
	}

	@Override
	public String getDescription() {

		return description;
	}

	@Override
	public ImageDescriptor getIcon() {

		return icon.get();
	}

	@Override
	public void transform(List<EObject> selectedObjects) {

		Method method = findMatchingMethod(selectedObjects);

		if (method == null) {
			throw new DeltaJException("Invalid selection. No matching tranformation method found.");
		}

		method.setAccessible(true);

		try {
			method.invoke(this, selectedObjects.toArray());
		} catch (IllegalArgumentException exception) {
			throw new DeltaJException(exception, "Internal error: IllegalArgumentException");
		} catch (IllegalAccessException exception) {
			throw new DeltaJException(exception, "Internal error: IllegalAccessException.");
		} catch (InvocationTargetException exception) {
			throw new DeltaJException(
					exception.getTargetException(),
					"Internal error during transformation. See error output for more information.");
		}
	}

	@Override
	public boolean isValidSelection(List<EObject> selectedObjects) {

		return findMatchingMethod(selectedObjects) != null;
	}

	private Method findMatchingMethod(List<EObject> selectedObjects) {

		return ReflectionUtils.findMatchingMethod(this, "transform", selectedObjects);
	}
}
