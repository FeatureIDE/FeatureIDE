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
package de.ovgu.featureide.ui.statistics.ui;

import static de.ovgu.featureide.fm.core.localization.StringTable.AVERAGE;
import static de.ovgu.featureide.fm.core.localization.StringTable.CALCULATE;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONFIGURATION_DIALOG;
import static de.ovgu.featureide.fm.core.localization.StringTable.HIGH;
import static de.ovgu.featureide.fm.core.localization.StringTable.HIGH_TO_THREAD_MAX_PRIORITY_;
import static de.ovgu.featureide.fm.core.localization.StringTable.INVALID_SELECTION_;
import static de.ovgu.featureide.fm.core.localization.StringTable.LOW;
import static de.ovgu.featureide.fm.core.localization.StringTable.MAXIMUM_DURATION_OF_THE_CALCULATION_IN_SECONDS_;
import static de.ovgu.featureide.fm.core.localization.StringTable.YOUR_CHOOSEN_TIMEOUT_MAY_NOT_BE_ENOUGH_TO_SHOW_THE_EXACT_RESULT_;

import java.util.concurrent.TimeUnit;

import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.dialogs.TitleAreaDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * This dialog will show up for the calculation of the complexity of a feature model. Here you can set the priority and the timeout.
 *
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public class ConfigDialog extends TitleAreaDialog {

	private static final String MINUTE = "60";

	private int priority;
	private long timeout;

	private Combo timeOutComboBox;
	private Combo priorityComboBox;
	private Text converterToMinutes;
	private Composite container;
	private final String titlePart;

	public int getPriority() {
		return priority;
	}

	public long getTimeout() {
		return timeout;
	}

	/**
	 * Create the dialog.
	 *
	 * @param parentShell
	 */
	public ConfigDialog(Shell parentShell, String titlePart) {
		super(parentShell);
		this.titlePart = titlePart.toLowerCase();
	}

	@Override
	protected void configureShell(Shell newShell) {
		super.configureShell(newShell);
		newShell.setText(CONFIGURATION_DIALOG);
		newShell.setImage(GUIDefaults.FEATURE_SYMBOL);
	}

	/**
	 * Create contents of the dialog.
	 *
	 * @param parent
	 */
	@Override
	protected Control createDialogArea(Composite parent) {

		setHelpAvailable(false);
		setMessage("In this dialog you can set the options for the calculation. Be aware that\n"
			+ YOUR_CHOOSEN_TIMEOUT_MAY_NOT_BE_ENOUGH_TO_SHOW_THE_EXACT_RESULT_);
		setTitle(CALCULATE + titlePart);
		container = (Composite) super.createDialogArea(parent);
		final GridLayout gl_container = new GridLayout(2, false);
		container.setLayout(gl_container);
		new Label(container, SWT.NONE);

		final Label priorityLabel = new Label(container, SWT.NONE);
		priorityLabel.setText(" Choose priority:");

		createPriorityComboBox();

		final Label timeOutLabel = new Label(container, SWT.NONE);
		timeOutLabel.setText(" Choose timeout-length:");

		createTimeOutComboBox();

		createConverter();

		convertToReadable();
		return container;
	}

	private void createConverter() {
		converterToMinutes = new Text(container, SWT.BORDER);
		converterToMinutes.setEditable(false);
		final GridData gd_text_1 = new GridData(SWT.RIGHT, SWT.TOP, false, false, 1, 1);
		gd_text_1.heightHint = 20;
		gd_text_1.widthHint = 175;
		converterToMinutes.setLayoutData(gd_text_1);
	}

	private void createTimeOutComboBox() {
		timeOutComboBox = new Combo(container, SWT.NONE);
		timeOutComboBox.addSelectionListener(new SelectionAdapter() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				convertToReadable();
			}
		});
		timeOutComboBox.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {
				convertToReadable();
			}
		});
		timeOutComboBox.setToolTipText(MAXIMUM_DURATION_OF_THE_CALCULATION_IN_SECONDS_);
		timeOutComboBox.setTextLimit(300000);

		timeOutComboBox.setItems(new String[] { "1", "10", "30", MINUTE, "180", "300", "900", "1800", "3600" });

		final GridData gd_timeOutComboBox = new GridData(SWT.RIGHT, SWT.TOP, false, false, 1, 1);
		gd_timeOutComboBox.widthHint = 160;
		gd_timeOutComboBox.heightHint = 20;
		timeOutComboBox.setLayoutData(gd_timeOutComboBox);
		timeOutComboBox.select(3);
		new Label(container, SWT.NONE);
	}

	private void createPriorityComboBox() {
		priorityComboBox = new Combo(container, SWT.READ_ONLY);
		priorityComboBox.setToolTipText("Priority of the calculation.\n" + "Low coresponds to Thread.MIN_PRIORITY,\n" + "Average to Thread.NORM_PRIORITY and\n"
			+ HIGH_TO_THREAD_MAX_PRIORITY_);
		priorityComboBox.setItems(new String[] { LOW, AVERAGE, HIGH });
		final GridData gd_combo = new GridData(SWT.RIGHT, SWT.TOP, false, false, 1, 1);
		gd_combo.heightHint = 20;
		gd_combo.widthHint = 160;
		priorityComboBox.setLayoutData(gd_combo);
		priorityComboBox.select(1);
	}

	private void convertToReadable() {
		try {
			final long time = Long.parseLong(timeOutComboBox.getText());
			converterToMinutes.setText(String.format("%02d h %02d min %02d sec", TimeUnit.SECONDS.toHours(time),
					TimeUnit.SECONDS.toMinutes(time) - TimeUnit.HOURS.toMinutes(TimeUnit.SECONDS.toHours(time)),
					time - TimeUnit.MINUTES.toSeconds(TimeUnit.SECONDS.toMinutes(time))));
		} catch (final NumberFormatException ex) {

		} catch (final NullPointerException ex) {

		}
	}

	/**
	 * Create contents of the button bar.
	 *
	 * @param parent
	 */
	@Override
	protected void createButtonsForButtonBar(Composite parent) {
		createButton(parent, IDialogConstants.OK_ID, IDialogConstants.OK_LABEL, true);
		createButton(parent, IDialogConstants.CANCEL_ID, IDialogConstants.CANCEL_LABEL, false);
	}

	@Override
	protected void okPressed() {
		final String p = priorityComboBox.getText();
		if (p.equals(LOW)) {
			priority = Job.DECORATE;
		} else if (p.equals(AVERAGE)) {
			priority = Job.LONG;
		} else if (p.equals(HIGH)) {
			priority = Job.SHORT;
		} else {
			throw new RuntimeException(INVALID_SELECTION_);
		}

		final String t = timeOutComboBox.getText();
		try {
			timeout = 1000 * Long.parseLong(t);
		} catch (final NumberFormatException ex) {
			MessageDialog.openError(Display.getDefault().getActiveShell(), "Error", "That was not a valid number!\n(integer only)");
			return;
		}

		super.okPressed();
	}

	/**
	 * Return the initial size of the dialog.
	 */
	@Override
	protected Point getInitialSize() {
		return new Point(469, 313);
	}
}
