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
package de.ovgu.featureide.fm.ui.views.constraintview.util;

import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CLabel;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.RowData;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Dialog;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.Preferences;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.views.constraintview.ConstraintViewController;

/**
 * A dialog that asks a user to open the constraint view. Its saves the decision in the workspace wide preferences.
 *
 * @author "Rosiak Kamil"
 */
public class ConstraintViewDialog extends Dialog {
	public static final String CONSTRAINT_VIEW_REMEMBER = "de.ovgu.featureide.fm.ui.views.constraintview_remember";
	public static final String CONSTRAINT_VIEW_DECISION = "de.ovgu.featureide.fm.ui.views.constraintview_decision";

	private final int ROW_WIDTH = 120;
	private Shell shell;
	private static boolean remember;
	private static boolean decision;
	private int exitCode = SWT.CANCEL;

	// default constructor
	public ConstraintViewDialog(Shell parent) {
		this(parent, SWT.DIALOG_TRIM | SWT.APPLICATION_MODAL | SWT.Resize);
		shell = parent;
		remember = Boolean.parseBoolean(Preferences.getPref(ConstraintViewDialog.CONSTRAINT_VIEW_REMEMBER, "false"));
		decision = Boolean.parseBoolean(Preferences.getPref(ConstraintViewDialog.CONSTRAINT_VIEW_DECISION, "false"));
	}

	public ConstraintViewDialog(Shell parent, int style) {
		super(parent, style);
		shell = parent;
	}

	public boolean getDecision() {
		return decision;
	}

	public boolean isRemember() {
		return remember;
	}

	/**
	 * Opens the dialog.
	 *
	 * @return exit code SWT.OK | SWT.NO | SWT.CANCEL
	 */
	public int open() {
		shell.setText(StringTable.CONSTRAINT_VIEW_QUESTION_TITLE);
		shell.setLocation(Display.getCurrent().getCursorLocation());
		createContents(shell);
		shell.pack();
		shell.open();

		final Display display = getParent().getDisplay();
		while (!shell.isDisposed()) {
			if (!display.readAndDispatch()) {
				display.sleep();
			}
		}
		return exitCode;
	}

	/**
	 * Creates the dialog's contents
	 *
	 * @param shell the dialog window
	 */
	private void createContents(final Shell shell) {
		shell.setLayout(new RowLayout(SWT.VERTICAL));

		// Question text
		final CLabel label = new CLabel(shell, SWT.NONE);
		label.setText(StringTable.CONSTRAINT_VIEW_QUESTION_DIALOG);
		label.setImage(shell.getDisplay().getSystemImage(SWT.ICON_QUESTION));

		// Buttons and Layouting
		final Button rememberDecButton = new Button(shell, SWT.CHECK);
		rememberDecButton.setText(StringTable.CONSTRAINT_VIEW_REMEMBER_DECISION);
		rememberDecButton.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent event) {
				remember = rememberDecButton.getSelection();
			}
		});

		final Composite buttons = new Composite(shell, SWT.None);
		buttons.setLayout(new RowLayout(SWT.HORIZONTAL));
		final RowData rowData = new RowData();
		rowData.width = ROW_WIDTH;

		final Button cancelButton = new Button(buttons, SWT.PUSH);
		cancelButton.setText(StringTable.CANCEL);
		cancelButton.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent event) {
				setExitCode(SWT.CANCEL);
				shell.dispose();
			}
		});

		final Button noButton = new Button(buttons, SWT.PUSH);
		noButton.setText(StringTable.NO);
		noButton.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent event) {
				if (remember) {
					Preferences.store(CONSTRAINT_VIEW_REMEMBER, "true");
					Preferences.store(CONSTRAINT_VIEW_DECISION, "false");
					decision = false;
				}
				setExitCode(SWT.NO);
				shell.dispose();
			}
		});

		final Button yesButton = new Button(buttons, SWT.PUSH);
		yesButton.setText(StringTable.YES);

		yesButton.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent event) {
				if (remember) {
					Preferences.store(CONSTRAINT_VIEW_REMEMBER, "true");
					Preferences.store(CONSTRAINT_VIEW_DECISION, "true");
					decision = true;
				}
				setExitCode(SWT.YES);
				try {
					PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().showView(ConstraintViewController.ID);
				} catch (final PartInitException e) {
					e.printStackTrace();
				}
				shell.dispose();
			}
		});
		cancelButton.setLayoutData(rowData);
		yesButton.setLayoutData(rowData);
		noButton.setLayoutData(rowData);
		shell.setDefaultButton(cancelButton);
	}

	private void setExitCode(int exitCode) {
		this.exitCode = exitCode;
	}

}
