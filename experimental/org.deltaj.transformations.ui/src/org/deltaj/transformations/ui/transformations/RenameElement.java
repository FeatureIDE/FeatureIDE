package org.deltaj.transformations.ui.transformations;

import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.Product;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.transformations.rename.DeltaJFeatureRenamer;
import org.deltaj.transformations.rename.DeltaJModuleRenamer;
import org.deltaj.transformations.rename.DeltaJProductLineRenamer;
import org.deltaj.transformations.rename.DeltaJProductRenamer;
import org.deltaj.transformations.ui.menu.IconEnum;
import org.deltaj.transformations.ui.transformation.AbstractTransformationCommandHandler;
import org.eclipse.jface.dialogs.IInputValidator;
import org.eclipse.jface.dialogs.InputDialog;
import org.eclipse.jface.window.Window;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;

class RenameElement extends AbstractTransformationCommandHandler {

	public RenameElement() {

		super("Rename Element", IconEnum.RENAME, "Renames the selected element.");
	}

	void transform(DeltaModule delta) {

		String newName = askForNewName(delta.getName());
		if (newName != null) {
			new DeltaJModuleRenamer(delta, newName).rename();
		}
	}

	void transform(ProductLine productLine) {

		String newName = askForNewName(productLine.getName());
		if (newName != null) {
			new DeltaJProductLineRenamer(productLine, newName).rename();
		}
	}

	void transform(Product product) {

		String newName = askForNewName(product.getName());
		if (newName != null) {
			new DeltaJProductRenamer(product, newName).rename();
		}
	}

	void transform(Feature feature) {

		String newName = askForNewName(feature.getName());
		if (newName != null) {
			new DeltaJFeatureRenamer(feature, newName).rename();
		}
	}

	private String askForNewName(String currentName) {

		Shell activeShell = Display.getCurrent().getActiveShell();
		InputDialog dialog = new InputDialog(
				activeShell,
				"Rename Element",
				"Enter the new name:",
				currentName,
				new IInputValidator() {

					@Override
					public String isValid(String newName) {

						if (newName.trim().isEmpty()) {
							return "Invalid name.";
						} else {
							return null;
						}
					}
				});

		int result = dialog.open();
		return result == Window.OK? dialog.getValue().trim() : null;
	}
}
