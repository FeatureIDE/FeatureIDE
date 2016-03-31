package de.ovgu.featureide.munge.ui.handlers;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.munge.MungePreprocessor;
import de.ovgu.featureide.ui.handlers.base.AFeatureProjectHandler;

public class EnableSignatureHandler extends AFeatureProjectHandler {

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.handlers.base.AFeatureProjectHandler#singleAction(de.ovgu.featureide.core.IFeatureProject)
	 */
	@Override
	protected void singleAction(IFeatureProject featureProject) {
		final IComposerExtensionClass composer = featureProject.getComposer();

		if (MungePreprocessor.COMPOSER_ID.equals(composer.getId())) {
			MungePreprocessor mungePreprocessor = (MungePreprocessor) composer;
			mungePreprocessor.setCreateSignature(!mungePreprocessor.getCreateSignature());
		}
	}


}
