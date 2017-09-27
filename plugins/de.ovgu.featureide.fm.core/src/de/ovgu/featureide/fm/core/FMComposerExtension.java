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
package de.ovgu.featureide.fm.core;

import org.eclipse.core.resources.IProject;

/**
 * Default feature model extension.
 *
 * @author Jens Meinicke
 */
public class FMComposerExtension implements IFMComposerExtension {

	private boolean hasComposer = false;

	public static final String FEATURE_NAME_PATTERN = "^[a-zA-Z]+\\w*$";

	@Override
	public String getOrderPageMessage() {
		return "";
	}

	@Override
	public boolean hasFeatureOrder() {
		return true;
	}

	@Override
	public boolean performRenaming(String oldName, String newName, IProject project) {
		return false;
	}

	@Override
	public final boolean isValidFeatureName(String s) {
		if ((s == null) || s.trim().isEmpty() || s.contains("\"") || s.contains("(") || s.contains(")")) {
			return false;
		} else {
			if (hasComposer) {
				final boolean valid = isValidFeatureNameComposerSpecific(s);
				return valid;
			} else {
				return true;
			}
		}
	}

	protected boolean isValidFeatureNameComposerSpecific(String s) {
		return s.matches(FEATURE_NAME_PATTERN);
	}

	@Override
	public final void hasComposer(boolean hasComposer) {
		this.hasComposer = hasComposer;
	}

	@Override
	public String getErrorMessage() {
		return hasComposer ? ERROR_MESSAGE_COMPOSER : ERROR_MESSAGE_NO_COMPOSER;
	}
}
