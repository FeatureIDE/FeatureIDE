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

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;

/**
 *
 * @author Sebastian Krieter
 */
public class FeatureModelConversionPage extends AbstractWizardPage {

	private final class DialogChangedListener implements ModifyListener {

		@Override
		public void modifyText(ModifyEvent e) {
			updatePage();
		}
	}

	protected Text outputPath;

	protected Combo fromFormatCombo;
	protected Combo toFormatCombo;

	public FeatureModelConversionPage() {
		super("Specfiy Conversion Settings");
		setDescription("Converts the File Format of Feature Model Files");
	}

	@Override
	public void createControl(Composite parent) {
		final Composite container = new Composite(parent, SWT.NULL);
		final GridLayout gridLayout = new GridLayout();
		gridLayout.numColumns = 1;
		container.setLayout(gridLayout);
		setControl(container);

		final Group toolGroup = new Group(container, SWT.NONE);
		toolGroup.setText("Format Conversion:");
		toolGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		final GridLayout projGridLayout = new GridLayout();
		projGridLayout.numColumns = 2;
		toolGroup.setLayout(projGridLayout);

		new Label(toolGroup, SWT.NONE).setText("From:");
		new Label(toolGroup, SWT.NONE).setText("To:");
		fromFormatCombo = new Combo(toolGroup, SWT.READ_ONLY | SWT.DROP_DOWN);
		fromFormatCombo.setLayoutData(new GridData(GridData.FILL_BOTH));
		toFormatCombo = new Combo(toolGroup, SWT.READ_ONLY | SWT.DROP_DOWN);
		toFormatCombo.setLayoutData(new GridData(GridData.FILL_BOTH));

		for (final IFeatureModelFormat format : FMFormatManager.getInstance().getExtensions()) {
			fromFormatCombo.add(format.getId());
			toFormatCombo.add(format.getId());
		}

		if (fromFormatCombo.getItems().length > 0) {
			fromFormatCombo.select(0);
			toFormatCombo.select(0);
		}

		// Path Group
		final Group pathGroup = new Group(container, SWT.NONE);
		final GridLayout layout = new GridLayout();
		final GridData gd = new GridData(GridData.FILL_HORIZONTAL);
		layout.numColumns = 2;
		layout.verticalSpacing = 9;
		pathGroup.setText("Output Path:");
		pathGroup.setLayoutData(gd);
		pathGroup.setLayout(layout);

		outputPath = new Text(pathGroup, SWT.BORDER | SWT.SINGLE);
		outputPath.setLayoutData(gd);
		outputPath.setText("converted");

		addListeners();
		updatePage();
	}

	protected void addListeners() {
		outputPath.addModifyListener(new DialogChangedListener());
	}

	@Override
	protected String checkPage() {
		final String text = outputPath.getText();
		try {
			final Path path = Paths.get(text);
			if (Files.isDirectory(path)) {
				return (text + " is not a directory!");
			}
			if (Files.exists(path)) {
				setMessage("Directory already exists. Files will be overridden!", WARNING);
			}
		} catch (InvalidPathException | NullPointerException ex) {
			return (text + " is not a valid path name!");
		}
		return super.checkPage();
	}

	@Override
	protected void putData() {
		abstractWizard.putData(WizardConstants.KEY_OUT_FOLDER, outputPath.getText());
		int selectionIndex = fromFormatCombo.getSelectionIndex();
		abstractWizard.putData(WizardConstants.KEY_OUT_INPUTFORMAT, selectionIndex >= 0 ? fromFormatCombo.getItem(selectionIndex) : null);
		selectionIndex = toFormatCombo.getSelectionIndex();
		abstractWizard.putData(WizardConstants.KEY_OUT_OUTPUTFORMAT, selectionIndex >= 0 ? toFormatCombo.getItem(selectionIndex) : null);
	}

}
