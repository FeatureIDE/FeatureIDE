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
package de.ovgu.featureide.ui.mpl.wizards;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;
import org.eclipse.swt.widgets.Widget;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;

/**
 * A dialog page for the {@link NewMultiFeatureProjectWizard}.
 * 
 * @author Sebastian Krieter
 */
public class NewMultiFeatureProjectPage extends WizardPage {

	protected Table projectTable;
	protected HashMap<Widget, IFeatureProject> map = new HashMap<Widget, IFeatureProject>();
	protected HashSet<IFeatureProject> sel = new HashSet<IFeatureProject>();
	
	protected NewMultiFeatureProjectPage() {
		super("");
		setTitle("Select a composer");
		setDescription("Creates a Multi-FeatureIDE project");
	}

	public void createControl(Composite parent) {
		Composite container = new Composite(parent, SWT.NULL);
		final GridLayout gridLayout = new GridLayout();
		gridLayout.numColumns = 1;
		container.setLayout(gridLayout);
		setControl(container);

		Group toolGroup = new Group(container, SWT.NONE);
		toolGroup.setText("Feature Project Selection:");
		toolGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		GridLayout projGridLayout = new GridLayout();
		projGridLayout.numColumns = 2;
		toolGroup.setLayout(projGridLayout);

		final Label helloLabel = new Label(toolGroup, SWT.NONE);
		GridData gridData = new GridData(GridData.FILL_BOTH);
		gridData.horizontalSpan = 2;
		helloLabel.setLayoutData(gridData);
		helloLabel.setText("Please select two or more projects from below.");

		projectTable = new Table(toolGroup, SWT.CHECK | SWT.BORDER | SWT.V_SCROLL | SWT.H_SCROLL);
		projectTable.setLayoutData(new GridData(GridData.FILL_BOTH));

		projectTable.setHeaderVisible(true);
		projectTable.setLinesVisible(true);
		TableColumn column = new TableColumn(projectTable, SWT.NONE);
		column.setText("Projects");
		column.setResizable(true);
		column.setMoveable(false);

		for (IFeatureProject p : CorePlugin.getFeatureProjects()) {
			TableItem item = new TableItem(projectTable, SWT.NONE);
			item.setText(p.getProjectName());
			item.setText(0, p.getProjectName());
			map.put(item, p);			
		}
		column.pack();

		addListeners();
		dialogChanged();
	}
	
	public Collection<IFeatureProject> getProjects() {
		return sel;
	}

	private void addListeners() {
		projectTable.addSelectionListener(new SelectionListener() {	
			@Override
			public void widgetSelected(SelectionEvent e) {
				if (e.detail == SWT.CHECK) {
					IFeatureProject p = map.get(e.item);
					if (sel.contains(p)) {
						sel.remove(p);
					} else {
						sel.add(p);
					}
					dialogChanged();
				}
			}
			
			@Override
			public void widgetDefaultSelected(SelectionEvent e) {
			}
		});
	}

	protected void dialogChanged() {
		if (sel.size() == 0) {
			updateStatus("Select at least one project");
		} else {
			updateStatus(null);
		}
	}
	
	protected void updateStatus(String message) {
		setErrorMessage(message);
		setPageComplete(message == null);
	}
}
