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
package de.ovgu.featureide.core.mspl.wizard;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeItem;

import de.ovgu.featureide.core.builder.FeatureProjectNature;
import de.ovgu.featureide.core.mspl.MSPLNature;

/**
 * A wizard page to select the project the user wants to import from. Shows all
 * project in workbench.
 * 
 * @author Christoph Giesel
 */
public class SelectProjectWizardPage extends WizardPage implements
		SelectionListener {

	private Composite container;
	private Tree projectTree;

	public SelectProjectWizardPage() {
		super("Select Project");
		setTitle("Select Project");
		setDescription("Here you select the project you want to import from.");
		setControl(projectTree);
	}

	@Override
	public void createControl(Composite parent) {
		container = new Composite(parent, SWT.NONE);

		GridLayout layout = new GridLayout();
		container.setLayout(layout);

		projectTree = new Tree(container, SWT.NORMAL);
		projectTree.addSelectionListener(this);

		IProject[] projects = ResourcesPlugin.getWorkspace().getRoot()
				.getProjects();

		for (IProject project : projects) {
			try {
				if (!project.isNatureEnabled(FeatureProjectNature.NATURE_ID)
						|| project.isNatureEnabled(MSPLNature.NATURE_ID))
					continue;
			} catch (CoreException e) {
				continue;
			}

			TreeItem item = new TreeItem(projectTree, SWT.NORMAL);
			item.setText(project.getName());
			item.setData(project);
		}

		// Required to avoid an error in the system
		setControl(container);
		setPageComplete(projectTree.getSelectionCount() == 1);
	}

	/**
	 * returns the project of the selected item
	 * 
	 * @return null if no item is selected, otherwise the project of the
	 *         selected Item
	 */
	public IProject getSelectedProject() {
		TreeItem[] items = projectTree.getSelection();

		if (items.length == 0)
			return null;

		return (IProject) items[0].getData();
	}

	@Override
	public void widgetSelected(SelectionEvent e) {
		setPageComplete(projectTree.getSelectionCount() == 1);
	}

	@Override
	public void widgetDefaultSelected(SelectionEvent e) {
	}

}
