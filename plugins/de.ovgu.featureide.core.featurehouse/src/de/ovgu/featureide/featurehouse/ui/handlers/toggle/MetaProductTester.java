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
package de.ovgu.featureide.featurehouse.ui.handlers.toggle;

import org.eclipse.core.commands.State;
import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.core.resources.IProject;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.handlers.RegistryToggleState;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.featurehouse.FeatureHouseComposer;
import de.ovgu.featureide.fm.ui.handlers.base.SelectionWrapper;

/**
 * Sets the toggle state of the metaproduct command in the UI.
 *
 * @author Sebastian Krieter
 */
public class MetaProductTester extends PropertyTester {

	@Override
	public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
		// Cast is necessary, don't remove
		final State state =
			((ICommandService) PlatformUI.getWorkbench().getService(ICommandService.class)).getCommand((String) args[0]).getState(RegistryToggleState.STATE_ID);
		final IProject curProject = SelectionWrapper.init((IStructuredSelection) receiver, IProject.class).getNext();
		if (curProject != null) {
			final IFeatureProject featureProject = CorePlugin.getFeatureProject(curProject);
			if (featureProject != null) {
				final IComposerExtensionClass composer = featureProject.getComposer();
				if (FeatureHouseComposer.COMPOSER_ID.equals(composer.getId())) {
					state.setValue(((FeatureHouseComposer) composer).buildMetaProduct());
					return true;
				}
			}
		}
		state.setValue(false);
		return true;
	}

}
