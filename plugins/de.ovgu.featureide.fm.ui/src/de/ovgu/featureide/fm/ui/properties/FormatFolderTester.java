/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.base.impl.FormatManager;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.handlers.base.SelectionWrapper;

public class FormatFolderTester extends PropertyTester {

	public FormatFolderTester() {}

	@Override
	public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
		final IContainer res = SelectionWrapper.checkClass(receiver, IContainer.class);
		if (res != null) {
			final List<IFile> files = new ArrayList<>();
			try {
				res.accept(new IResourceVisitor() {

					@Override
					public boolean visit(IResource child) throws CoreException {
						if (child instanceof IFile) {
							files.add((IFile) child);
						}
						return true;
					}
				}, IResource.DEPTH_ONE, IResource.NONE);
				if (!files.isEmpty()) {
					final FormatManager<?> formatManager = getFormatManager(property);
					final FormatTester formatTester = new FormatTester();
					for (final IFile file : files) {
						if (formatTester.checkFormat(formatManager, file, expectedValue)) {
							return true;
						}
					}
				}
			} catch (final CoreException e) {
				FMUIPlugin.getDefault().logError(e);
			}

		}
		return false;
	}

	private FormatManager<?> getFormatManager(String property) {
		switch (property) {
		case "featureModelFolder":
			return FMFormatManager.getInstance();
		case "configurationFolder":
			return ConfigFormatManager.getInstance();
		default:
			return null;
		}
	}

}
