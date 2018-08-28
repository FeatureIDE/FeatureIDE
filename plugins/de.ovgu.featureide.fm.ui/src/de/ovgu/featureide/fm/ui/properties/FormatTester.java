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
package de.ovgu.featureide.fm.ui.properties;

import java.nio.file.Paths;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.base.impl.FormatManager;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.ui.handlers.base.SelectionWrapper;

public class FormatTester extends PropertyTester {

	@Override
	public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
		final IFile res = SelectionWrapper.checkClass(receiver, IFile.class);
		return checkFormat(getFormatManager(property), res, expectedValue);
	}

	protected boolean checkFormat(final FormatManager<?> formatManager, final IFile res, Object expectedValue) {
		if (res != null) {
			if (formatManager != null) {
				final IPersistentFormat<?> formatByContent = formatManager.getFormatByContent(Paths.get(res.getLocationURI()));
				return (expectedValue == null) ? formatByContent != null : expectedValue.equals(formatByContent.getId());
			}
		}
		return false;
	}

	private FormatManager<?> getFormatManager(String property) {
		switch (property) {
		case "featuremodel":
			return FMFormatManager.getInstance();
		case "configuration":
			return ConfigFormatManager.getInstance();
		default:
			return null;
		}
	}

}
