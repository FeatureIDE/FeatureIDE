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
package de.ovgu.featureide.fm.ui;

import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.init.ILibrary;
import de.ovgu.featureide.fm.core.io.ExternalChangeListener;
import de.ovgu.featureide.fm.ui.editors.EclipseExternalChangeListener;
import de.ovgu.featureide.fm.ui.editors.elements.GraphicalFeatureModelFormat;
import de.ovgu.featureide.fm.ui.editors.elements.GraphicalFeatureModelFormatManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationApprover;

/**
 * The library object for the fm.ui plug-in when using the Eclipse platform.
 *
 * @author Sebastian Krieter
 */
public class FMUIEclipseLibrary implements ILibrary {

	private static FMUIEclipseLibrary instance;

	public static FMUIEclipseLibrary getInstance() {
		if (instance == null) {
			instance = new FMUIEclipseLibrary();
		}
		return instance;
	}

	private FMUIEclipseLibrary() {}

	private EclipseExternalChangeListener eclipseExternalChangeListener;
	private FeatureModelOperationApprover featureModelOperationApprover;

	@Override
	public void install() {
		GraphicalFeatureModelFormatManager.getInstance().addExtension(new GraphicalFeatureModelFormat());

		eclipseExternalChangeListener = new EclipseExternalChangeListener();
		ExternalChangeListener.listener = eclipseExternalChangeListener;
		ResourcesPlugin.getWorkspace().addResourceChangeListener(eclipseExternalChangeListener);

		featureModelOperationApprover = new FeatureModelOperationApprover();
		PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().addOperationApprover(featureModelOperationApprover);
	}

	@Override
	public void uninstall() {
		if (eclipseExternalChangeListener != null) {
			ResourcesPlugin.getWorkspace().removeResourceChangeListener(eclipseExternalChangeListener);
			eclipseExternalChangeListener = null;
		}
		if (featureModelOperationApprover != null) {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().removeOperationApprover(featureModelOperationApprover);
			featureModelOperationApprover = null;
		}
	}

}
