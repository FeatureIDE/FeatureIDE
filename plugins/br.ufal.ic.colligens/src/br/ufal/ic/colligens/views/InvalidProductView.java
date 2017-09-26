package br.ufal.ic.colligens.views;

import static de.ovgu.featureide.fm.core.localization.StringTable.INVALID_PRODUCTS___COLLIGENS;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.part.ViewPart;

import br.ufal.ic.colligens.activator.Colligens;
import br.ufal.ic.colligens.controllers.invalidproducts.InvalidProductsViewController;

public class InvalidProductView extends ViewPart {

	public static final String ID = Colligens.PLUGIN_ID + ".views.InvalidConfigurationsView";
	private final InvalidProductsViewController controller;

	public InvalidProductView() {
		controller = InvalidProductsViewController.getInstance();
		controller.setView(this);
		setTitleToolTip(INVALID_PRODUCTS___COLLIGENS);
	}

	@Override
	public void createPartControl(Composite parent) {
		controller.createPartControl(parent);

	}

	@Override
	public void setFocus() {
		controller.setFocus();
	}

}
