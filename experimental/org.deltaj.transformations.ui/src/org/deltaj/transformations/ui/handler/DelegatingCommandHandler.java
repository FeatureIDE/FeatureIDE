package org.deltaj.transformations.ui.handler;

import java.util.List;
import org.deltaj.transformations.ui.selection.DeltaJSelection;
import org.deltaj.transformations.ui.selection.IModifyingSelectionHandler;
import org.deltaj.transformations.ui.selection.SelectionHandlerDelegator;
import org.deltaj.transformations.ui.transformation.ITransformationCommandHandler;
import org.deltaj.transformations.ui.transformations.TransformationEnum;
import org.deltaj.transformations.ui.utils.ExceptionUtils;
import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.handlers.HandlerUtil;

public class DelegatingCommandHandler extends AbstractHandler {

	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {

		DeltaJSelection deltaJSelection = getSelection(event);
		ITransformationCommandHandler transformation = getTransformation(event);

		try {
			return executeTransformation(deltaJSelection, transformation);
		} catch (Exception exception) {
			new ErrorDisplayer().showError(exception.getMessage());
			System.err.println(ExceptionUtils.getStackTraceAsString(exception));
			return null;
		}
	}

	private DeltaJSelection getSelection(ExecutionEvent event) {

		ISelection selection = HandlerUtil.getCurrentSelection(event);
		return DeltaJSelection.create(selection);
	}

	private ITransformationCommandHandler getTransformation(ExecutionEvent event) {

		String commandId = event.getCommand().getId();
		return TransformationEnum.getByCommandId(commandId).getCommandHandler();
	}

	// fetches the current selection and executes the given transformation on it
	private Object executeTransformation(DeltaJSelection deltaJSelection, final ITransformationCommandHandler transformation) {

		return new SelectionHandlerDelegator(deltaJSelection).delegate(new IModifyingSelectionHandler<Void>() {

			@Override
			public Void handle(List<EObject> selectedObjects) {

				transformation.transform(selectedObjects);
				return null;
			}
		});
	}
}
