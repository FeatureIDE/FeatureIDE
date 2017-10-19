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
package de.ovgu.featureide.core.framework;

/**
 * Framework specific feature model extensions.
 *
 * @author Christopher Sontag
 */
public class FrameworkFMComposerExtension extends de.ovgu.featureide.fm.core.FMComposerExtension {

	private static String ORDER_PAGE_MESSAGE = "FeatureIDE projects based on frameworks do not support any order.";

	@Override
	public String getOrderPageMessage() {
		return ORDER_PAGE_MESSAGE;
	}

	@Override
	public boolean hasFeatureOrder() {
		return false;
	}

	/**
	 * Check for valid java identifier
	 */
	@Override
	protected boolean isValidFeatureNameComposerSpecific(String s) {
		// An empty or null string cannot be a valid identifier
		if ((s == null) || (s.length() == 0)) {
			return false;
		}

		final char[] c = s.toCharArray();
		if (!Character.isJavaIdentifierStart(c[0])) {
			return false;
		}

		for (int i = 1; i < c.length; i++) {
			if (!Character.isJavaIdentifierPart(c[i])) {
				return false;
			}
		}

		return true;
	}
}
