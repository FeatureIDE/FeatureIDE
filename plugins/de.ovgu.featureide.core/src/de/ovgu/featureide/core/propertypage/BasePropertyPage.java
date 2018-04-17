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
package de.ovgu.featureide.core.propertypage;

import static de.ovgu.featureide.fm.core.localization.StringTable.NO_RESOURCE_SELECTED;
import static de.ovgu.featureide.fm.core.localization.StringTable.RESTRICTION;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.internal.core.JavaElement;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.dialogs.PropertyPage;

/**
 * First FeatureIDE property page containing all other property pages at the sub tree
 *
 * @author Jens Meinicke
 */
@SuppressWarnings(RESTRICTION)
public class BasePropertyPage extends PropertyPage {

	private static final String DESCRIPTION = null;
	private IProject project;

	@Override
	protected Control createContents(Composite parent) {
		final Composite composite = new Composite(parent, SWT.NULL);
		final GridLayout layout = new GridLayout();
		layout.numColumns = 1;
		layout.verticalSpacing = 9;
		composite.setLayout(layout);

		if (!getProject()) {
			final Label label = new Label(composite, SWT.NULL);
			label.setText(NO_RESOURCE_SELECTED);
			return null;
		}

		final Label label = new Label(composite, SWT.NULL);
		label.setText("&Project: " + project.getName());

		return composite;
	}

	/**
	 * Gets the project of the selected resource.
	 *
	 * @return <code>true</code> if successful
	 */
	private boolean getProject() {
		final IAdaptable resource = getElement();
		if (resource instanceof JavaElement) {
			final IJavaProject javaProject = ((JavaElement) resource).getJavaProject();
			project = javaProject.getProject();
		} else if (resource instanceof IResource) {
			project = ((IResource) resource).getProject();
		} else {
			return false;
		}
		return true;
	}

	@Override
	public String getDescription() {
		return DESCRIPTION;
	}

}
