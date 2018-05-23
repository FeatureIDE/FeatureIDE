/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.refactoring.windows;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.DisposeEvent;
import org.eclipse.swt.events.DisposeListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableItem;

import refactor.LayerInfo;
import de.ovgu.featureide.refactoring.GUIDefaults;
import de.ovgu.featureide.refactoring.typesystem.TypeSystemManager;

/**
 * A dialog to choose a destination layer for a Jak refactoring.
 * 
 * @author Stephan Kauschka
 */
public class ChooseLayerWindow implements SelectionListener, DisposeListener, GUIDefaults {

	private Window window;
	private Shell shell, parentshell;
	private Table table;
	private Button button;

	public ChooseLayerWindow(Shell parentShell, Window parentWindow) {
		this.window = parentWindow;
		this.parentshell = parentShell;
		this.shell = new Shell(parentShell, SWT.MIN);
		this.shell.setText("Choose a layer");
		this.shell.setImage(IMAGE_SAMPLE);
		this.shell.setSize(250, 200);
		this.shell.addDisposeListener(this);

		createGUI();
		parentShell.setEnabled(false);
		this.shell.open();
	}

	public void createGUI() {
		GridLayout layout = new GridLayout();
		layout.verticalSpacing = 5;
		layout.marginHeight = 10;
		layout.marginWidth = 10;
		layout.numColumns = 1;
		layout.makeColumnsEqualWidth = false;
		this.shell.setLayout(layout);

		this.table = new Table(this.shell, SWT.SINGLE | SWT.FULL_SELECTION
				| SWT.BORDER);
		this.table.setHeaderVisible(false);
		this.table.setLayoutData(new GridData(GridData.FILL_BOTH));

		try {
			LayerInfo[] infos = TypeSystemManager.getTypesystem(
					window.getProjectURI()).getLayer();

			for (int i = 0; i < infos.length; i++) {
				TableItem item = new TableItem(this.table, SWT.NONE);
				item.setText(infos[i].getFullName());
			}
		} catch (Exception e) {
			this.window.setText(Window.ERROR_TEXT, e.getMessage());
		}

		this.button = new Button(this.shell, SWT.CENTER);
		GridData a = new GridData(75, 25);
		a.horizontalAlignment = SWT.CENTER;
		this.button.setLayoutData(a);
		this.button.setText("Ok");
		this.button.addSelectionListener(this);
	}

	public void widgetDefaultSelected(SelectionEvent e) {
	}

	public void widgetSelected(SelectionEvent e) {
		try {
			if (e.getSource() == this.button) {
				String selection = (this.table.getSelection()[0]).getText();
				this.window.setText(Window.LAYER_TEXT, selection);
				this.shell.setVisible(false);
				this.shell.dispose();
				this.parentshell.setEnabled(true);
			}
		} catch (Exception ex) {
			this.shell.setVisible(false);
			this.shell.dispose();
			this.parentshell.setEnabled(true);
		}
	}

	public void widgetDisposed(DisposeEvent e) {
		this.parentshell.setEnabled(true);
	}
}
