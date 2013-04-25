package org.deltaj.transformations.ui.menu;

import java.util.List;
import org.deltaj.transformations.ui.selection.DeltaJSelection;
import org.deltaj.transformations.ui.selection.IReadOnlySelectionHandler;
import org.deltaj.transformations.ui.selection.SelectionHandlerDelegator;
import org.deltaj.transformations.ui.transformation.ITransformationCommandHandler;
import org.deltaj.transformations.ui.transformations.TransformationEnum;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.swt.SWT;
import org.eclipse.ui.ISelectionService;
import org.eclipse.ui.menus.CommandContributionItem;
import org.eclipse.ui.menus.CommandContributionItemParameter;
import org.eclipse.ui.menus.ExtensionContributionFactory;
import org.eclipse.ui.menus.IContributionRoot;
import org.eclipse.ui.services.IServiceLocator;

public class TransformationContributions extends ExtensionContributionFactory {

	@Override
	public void createContributionItems(IServiceLocator serviceLocator, IContributionRoot additions) {

		ISelectionService selectionService = (ISelectionService) serviceLocator.getService(ISelectionService.class);
		if (selectionService != null) {

			DeltaJSelection selection = DeltaJSelection.create(selectionService.getSelection());
			for (TransformationEnum transformationEnum: TransformationEnum.values()) {

				if (isValidSelection(transformationEnum, selection)) {
					CommandContributionItemParameter parameter = getParameters(serviceLocator, transformationEnum);
					addItem(additions, parameter);
				}
			}
		}
	}

	private CommandContributionItemParameter getParameters(IServiceLocator serviceLocator,
			TransformationEnum transformationEnum) {

		CommandContributionItemParameter parameter = new CommandContributionItemParameter(
				serviceLocator,
				"",
				transformationEnum.toString(),
				SWT.PUSH);

		ITransformationCommandHandler transformation = transformationEnum.getCommandHandler();
		parameter.label = transformation.getName();
		parameter.icon = transformation.getIcon();
		parameter.tooltip = transformation.getDescription();
		return parameter;
	}

	private void addItem(IContributionRoot additions, CommandContributionItemParameter parameter) {

		CommandContributionItem item = new CommandContributionItem(parameter);
		item.setVisible(true);
		additions.addContributionItem(item, null);
	}

	private static boolean isValidSelection(final TransformationEnum transformationEnum, DeltaJSelection selection) {

		Boolean result = new SelectionHandlerDelegator(selection).delegate(new IReadOnlySelectionHandler<Boolean>() {

			@Override
			public Boolean handle(List<EObject> selectedObjects) {

				return transformationEnum.getCommandHandler().isValidSelection(selectedObjects);
			}
		});

		return result != null && result;
	}
}
