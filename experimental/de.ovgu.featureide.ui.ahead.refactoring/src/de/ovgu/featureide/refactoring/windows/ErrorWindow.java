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
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

/**
 * Displays errors occurred while refactoring Jak files.
 * 
 * @author Stephan Kauschka
 */
public class ErrorWindow {

	private Display display;
	private Shell shell;
	private String msg, type;
	private Image errorImage = PlatformUI.getWorkbench().getSharedImages()
			.getImage(ISharedImages.IMG_OBJS_ERROR_TSK);

	public ErrorWindow(String errorType, String errorMessage) {
		this.msg = errorMessage;
		this.type = errorType;

		createGUI();
		while (!this.shell.isDisposed())
			if (!this.display.readAndDispatch())
				this.display.sleep();
	}

	public ErrorWindow(String errorType, String errorMessage,
			StackTraceElement[] stackTrace) {
		String trace = "";
		for (int i = 0; i < stackTrace.length; i++)
			trace = trace + stackTrace[i].toString() + "\n";

		this.msg = errorMessage + "\n\n" + trace;
		this.type = errorType;

		createGUI();
		while (!this.shell.isDisposed())
			if (!this.display.readAndDispatch())
				this.display.sleep();
	}

	private void createGUI() {
		this.display = Display.getCurrent();
		if (this.display == null)
			this.display = new Display();

		this.shell = new Shell(this.display, SWT.MIN);
		this.shell.setText("A(n) " + this.type + " occured ...");
		this.shell.setImage(errorImage);
		this.shell.setSize(500, 190);

		GridLayout layout = new GridLayout();
		layout.verticalSpacing = 5;
		layout.marginHeight = 5;
		layout.marginWidth = 5;
		layout.numColumns = 1;
		layout.makeColumnsEqualWidth = false;
		this.shell.setLayout(layout);

		Group group1 = new Group(this.shell, SWT.NONE);
		GridData g = new GridData(GridData.FILL_HORIZONTAL);
		g.heightHint = 105;
		group1.setLayoutData(g);
		group1.setLayout(new GridLayout());

		Text text = new Text(group1, SWT.WRAP | SWT.V_SCROLL);
		text.setBackground(this.shell.getBackground());
		text.setText(this.msg);
		text.setLayoutData(new GridData(GridData.FILL_BOTH));

		Button ok = new Button(this.shell, SWT.CENTER);
		ok.setText("Ok");
		ok.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {
				exit();
			}

			public void widgetSelected(SelectionEvent e) {
				exit();
			}
		});
		GridData g2 = new GridData();
		g2.horizontalAlignment = SWT.CENTER;
		g2.heightHint = 25;
		g2.widthHint = 75;
		ok.setLayoutData(g2);

		this.shell.open();
		if (text.getLineCount() < 7)
			text.getVerticalBar().setVisible(false);
	}

	private void exit() {
		this.shell.setVisible(false);
		this.shell.dispose();
	}

}
