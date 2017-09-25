package br.ufal.ic.colligens.views;

import java.util.List;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.part.ViewPart;

import br.ufal.ic.colligens.activator.Colligens;
import br.ufal.ic.colligens.controllers.metrics.MetricsViewController;
import br.ufal.ic.colligens.util.metrics.Metrics;

public class MetricsView extends ViewPart {

	public static final String ID = Colligens.PLUGIN_ID + ".views.MetricsView";
	private final MetricsViewController viewController;

	public MetricsView() {
		viewController = MetricsViewController.getInstance();
		viewController.setView(this);
	}

	@Override
	public void createPartControl(Composite parent) {
		viewController.createPartControl(parent);
	}

	public void setInput(List<Metrics> list) {
		viewController.setInput(list);
	}

	@Override
	public void setFocus() {
		viewController.setFocus();
	}

}
