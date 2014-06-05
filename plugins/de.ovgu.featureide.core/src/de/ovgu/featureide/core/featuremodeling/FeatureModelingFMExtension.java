/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.core.featuremodeling;

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

	private static String ORDER_PAGE_MESSAGE = 
			"FeatureIDE projects for modelling purpose only do not\n" +
			"need an order, as there is no source code to compose.";
	
	@Override
	public String getOrderPageMessage() {
		return ORDER_PAGE_MESSAGE;
	}
	
	@Override
	public boolean performRenaming(String oldName, String newName,
			IProject project) {
		return true;
	}

	@Override
	public boolean isValidFeatureName(String s) {
		if (s == null)
			return false;
		final int len = s.length();

		if (len == 0)
			return false;
		for (int i = 0; i < len; i++) {
			if (s.charAt(i) == '"' || s.charAt(i) == '(' || s.charAt(i) == ')')
				return false;
		}
		return true;
	}

	@Override
	public boolean hasFeaureOrder() {
		return false;
	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.FMComposerExtension#getErroMessage()
	 */
	@Override
	public String getErroMessage() {
		return ERROR_MESSAGE_NO_COMPOSER;
	}
}
