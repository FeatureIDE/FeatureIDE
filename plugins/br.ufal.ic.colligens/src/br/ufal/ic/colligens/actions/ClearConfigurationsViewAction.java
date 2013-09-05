package br.ufal.ic.colligens.actions;

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;

import br.ufal.ic.colligens.controllers.invalidconfigurations.InvalidConfigurationsViewController;

public class ClearConfigurationsViewAction extends PluginActions {

	@Override
	public void run(IAction action) {
		// TODO Auto-generated method stub
		InvalidConfigurationsViewController analyzerViewController = InvalidConfigurationsViewController
				.getInstance();

		analyzerViewController.clear();
	}

	@Override
	public void selectionChanged(IAction action, ISelection selection) {
		// TODO Auto-generated method stub
		InvalidConfigurationsViewController analyzerViewController = InvalidConfigurationsViewController
				.getInstance();
		
		action.setEnabled(!analyzerViewController.isEmpty());
	}

}
