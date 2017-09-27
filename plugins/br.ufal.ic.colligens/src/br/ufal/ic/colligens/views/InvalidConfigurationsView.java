package br.ufal.ic.colligens.views;

import static de.ovgu.featureide.fm.core.localization.StringTable.INVALID_CONFIGURATIONS___COLLIGENS;

import java.util.List;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.part.ViewPart;

import br.ufal.ic.colligens.activator.Colligens;
import br.ufal.ic.colligens.controllers.invalidconfigurations.InvalidConfigurationsViewController;
import br.ufal.ic.colligens.models.FileProxy;

public class InvalidConfigurationsView extends ViewPart {

	public static final String ID = Colligens.PLUGIN_ID + ".views.InvalidConfigurationsView";
	private final InvalidConfigurationsViewController viewController;

	public InvalidConfigurationsView() {
		viewController = InvalidConfigurationsViewController.getInstance();
		viewController.setView(this);
		setTitleToolTip(INVALID_CONFIGURATIONS___COLLIGENS);
	}

	@Override
	public void createPartControl(Composite parent) {
		viewController.createPartControl(parent);
	}

	public void setInput(List<FileProxy> logs) {
		viewController.setInput(logs);
	}

	@Override
	public void setFocus() {
		viewController.setFocus();
	}
}
