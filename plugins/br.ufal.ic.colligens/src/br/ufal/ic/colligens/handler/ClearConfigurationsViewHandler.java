/**
 *
 */
package br.ufal.ic.colligens.handler;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;

import br.ufal.ic.colligens.controllers.invalidconfigurations.InvalidConfigurationsViewController;

/**
 * @author Thiago Emmanuel
 *
 */
public class ClearConfigurationsViewHandler extends ColligensAbstractHandler {

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands. ExecutionEvent)
	 */
	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		final InvalidConfigurationsViewController analyzerViewController = InvalidConfigurationsViewController.getInstance();

		analyzerViewController.clear();
		return null;
	}

	@Override
	public boolean isEnabled() {
		final InvalidConfigurationsViewController analyzerViewController = InvalidConfigurationsViewController.getInstance();

		return !analyzerViewController.isEmpty();
	}

}
