package de.ovgu.featureide.munge.ui.handlers.toggle;

import org.eclipse.core.commands.State;
import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.core.resources.IProject;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.handlers.RegistryToggleState;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.fm.ui.handlers.base.SelectionWrapper;
import de.ovgu.featureide.munge.MungePreprocessor;

public class SignatureToggleTester extends PropertyTester {

	@Override
	public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
		final State state = ((ICommandService) PlatformUI.getWorkbench().getService(ICommandService.class)).getCommand((String) args[0]).getState(RegistryToggleState.STATE_ID);
		IProject curProject = SelectionWrapper.init((IStructuredSelection) receiver, IProject.class).getNext();
		if (curProject != null) {
			final IFeatureProject featureProject = CorePlugin.getFeatureProject(curProject);
			if (featureProject != null) {
				final IComposerExtensionClass composer = featureProject.getComposer();
				if (MungePreprocessor.COMPOSER_ID.equals(composer.getId())) {
					state.setValue(((MungePreprocessor) composer).getCreateSignature());
					return true;
				}
			}
		}
		state.setValue(false);
		return true;
	}

}
