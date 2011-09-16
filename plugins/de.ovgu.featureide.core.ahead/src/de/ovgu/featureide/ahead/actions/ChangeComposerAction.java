package de.ovgu.featureide.ahead.actions;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;

import de.ovgu.featureide.ahead.AheadComposer;

/**
 * 
 * A action to replace the composer of a given project.
 * 
 * @author Jens Meinicke
 */
public class ChangeComposerAction extends AbstractHandler {

	/**
	 * Calls the associated <code>ConversionAction</code> of the selected feature project.
	 */
	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		if (ComposerPropertyTester.getFeatureProject().getComposerID()
				.equals(AheadComposer.COMPOSER_ID)) {
			new AHEADToFeatureHouseConversion(ComposerPropertyTester.getFeatureProject());
		} else {
			new FeatureHouseToAHEADConversion(ComposerPropertyTester.getFeatureProject());
		}
		return null;
	}

}
