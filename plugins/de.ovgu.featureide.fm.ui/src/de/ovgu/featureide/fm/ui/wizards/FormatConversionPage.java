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
package de.ovgu.featureide.fm.ui.wizards;

import java.nio.file.Files;
import java.nio.file.InvalidPathException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.DirectoryDialog;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.fm.core.io.IPersistentFormat;

/**
 *
 * @author Sebastian Krieter
 */
public class FormatConversionPage extends AbstractWizardPage {

	private final class DialogChangedListener implements ModifyListener {

		@Override
		public void modifyText(ModifyEvent e) {
			updatePage();
		}
	}

	protected Text outputPathText;
	protected Button button;

	protected Combo fromFormatCombo;
	protected Combo toFormatCombo;

	protected List<? extends IPersistentFormat<?>> extensions = null;

	public FormatConversionPage() {
		super("Specfiy Conversion Settings");
		setDescription("Converts the File Format");
	}

	@Override
	public void createControl(Composite parent) {
		final Composite container = new Composite(parent, SWT.NULL);
		final GridLayout gridLayout = new GridLayout();
		gridLayout.numColumns = 1;
		container.setLayout(gridLayout);
		setControl(container);

		final Group toolGroup = new Group(container, SWT.NONE);
		toolGroup.setText("Export Format:");
		toolGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		final GridLayout projGridLayout = new GridLayout();
		projGridLayout.numColumns = 2;
		toolGroup.setLayout(projGridLayout);

		toFormatCombo = new Combo(toolGroup, SWT.READ_ONLY | SWT.DROP_DOWN);
		toFormatCombo.setLayoutData(new GridData(GridData.FILL_BOTH));

		extensions = ((FormatConversionWizard<?>) abstractWizard).formatManager.getExtensions();
		if (extensions != null) {
			for (final IPersistentFormat<?> format : extensions) {
				toFormatCombo.add(format.getName() + " (*." + format.getSuffix() + ")");
			}

			if (toFormatCombo.getItems().length > 0) {
				toFormatCombo.select(0);
			}
		}

		// Path Group
		final Group pathGroup = new Group(container, SWT.NONE);
		pathGroup.setText("Output Path:");
		pathGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		final GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		layout.verticalSpacing = 9;
		pathGroup.setLayout(layout);

		outputPathText = new Text(pathGroup, SWT.BORDER | SWT.SINGLE);
		outputPathText.setLayoutData(new GridData(GridData.FILL, GridData.FILL, true, true));

		final String homePath = System.getProperty("user.home");
		if (homePath != null) {
			outputPathText.setText(homePath);
		}

		button = new Button(pathGroup, SWT.PUSH);
		button.setText("Choose ...");
		button.setLayoutData(new GridData(SWT.RIGHT, GridData.FILL, false, true));

		addListeners();
		updatePage();
	}

	protected void addListeners() {
		outputPathText.addModifyListener(new DialogChangedListener());

		button.addSelectionListener(new SelectionListener() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				final DirectoryDialog fileDialog = new DirectoryDialog(new Shell(), SWT.SAVE);
				fileDialog.setFilterPath(".");

				// Ask for output folder
				final String outputPath = fileDialog.open();
				if (outputPath != null) {
					outputPathText.setText(outputPath);
				}
			}

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {}
		});
	}

	@Override
	protected String checkPage() {
		final String text = outputPathText.getText();
		try {
			final Path path = Paths.get(text);
			if (!Files.isDirectory(path)) {
				return (text + " is not a directory!");
			}
			if (Files.exists(path) && (path.toFile().listFiles().length > 0)) {
				setMessage("Directory is not empty. Exisiting files with the same name will be overridden!", WARNING);
			} else {
				setMessage(null);
			}
		} catch (InvalidPathException | NullPointerException ex) {
			return (text + " is not a valid path name!");
		}
		return super.checkPage();
	}

	@Override
	protected void putData() {
		abstractWizard.putData(WizardConstants.KEY_OUT_FOLDER, outputPathText.getText());
		final int selectionIndex = toFormatCombo.getSelectionIndex();
		abstractWizard.putData(WizardConstants.KEY_OUT_OUTPUTFORMAT, selectionIndex >= 0 ? extensions.get(selectionIndex) : null);
	}

}
