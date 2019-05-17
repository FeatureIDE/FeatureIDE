package de.ovgu.featureide.fm.attributes.composer;

import static de.ovgu.featureide.fm.core.localization.StringTable.NEED_AN_ORDER_COMMA__AS_THERE_IS_NO_SOURCE_CODE_TO_COMPOSE_;

import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.fm.core.FMComposerExtension;

public class ExtendedFeatureModelingFMExtension extends FMComposerExtension {

	private static final String FEATUREMODELLING_NAME_PATTERN = ".+";

	@Override
	protected boolean isValidFeatureNameComposerSpecific(String s) {
		return s.matches(FEATUREMODELLING_NAME_PATTERN);
	}

	private static String ORDER_PAGE_MESSAGE =
		"FeatureIDE projects for modelling purpose only do not\n" + NEED_AN_ORDER_COMMA__AS_THERE_IS_NO_SOURCE_CODE_TO_COMPOSE_;

	@Override
	public String getOrderPageMessage() {
		return ORDER_PAGE_MESSAGE;
	}

	@Override
	public boolean performRenaming(String oldName, String newName, IProject project) {
		return true;
	}

	@Override
	public String getErrorMessage() {
		return ERROR_MESSAGE_NO_COMPOSER;
	}

	@Override
	public boolean hasFeatureOrder() {
		return false;
	}
}
