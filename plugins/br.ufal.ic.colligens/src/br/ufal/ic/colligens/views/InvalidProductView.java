package br.ufal.ic.colligens.views;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.part.ViewPart;

import br.ufal.ic.colligens.activator.Colligens;
import br.ufal.ic.colligens.controllers.invalidproducts.InvalidProductsViewController;

public class InvalidProductView extends ViewPart {

	public static final String ID = Colligens.PLUGIN_ID
			+ ".views.invalideproductview";
	private InvalidProductsViewController controller;

	public InvalidProductView() {
		controller = InvalidProductsViewController.getInstance();
		controller.setView(this);
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
