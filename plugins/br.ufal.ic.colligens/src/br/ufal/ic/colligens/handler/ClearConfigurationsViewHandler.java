package br.ufal.ic.colligens.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;

import br.ufal.ic.colligens.controllers.invalidconfigurations.InvalidConfigurationsViewController;

public class ClearConfigurationsViewHandler extends AbstractHandler {

	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {

		InvalidConfigurationsViewController analyzerViewController = InvalidConfigurationsViewController
				.getInstance();

		analyzerViewController.clear();

		return null;
	}

}
