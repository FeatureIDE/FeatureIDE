/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 *
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.core.featuremodeling;

import static de.ovgu.featureide.fm.core.localization.StringTable.NEED_AN_ORDER_COMMA__AS_THERE_IS_NO_SOURCE_CODE_TO_COMPOSE_;

import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.fm.core.FMComposerExtension;

/**
 * FMComposerExtension for the Feature Modeling extension.
 *
 * @author Jens Meinicke
 * @author Florian Proksch
 * @author Stefan Krueger
 */
public class FeatureModelingFMExtension extends FMComposerExtension {

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
