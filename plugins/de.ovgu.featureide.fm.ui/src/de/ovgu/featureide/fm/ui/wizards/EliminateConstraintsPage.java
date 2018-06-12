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

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
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
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.ui.wizards.EliminateConstraintsWizard.ConversionMethod;

/**
 * TODO description
 *
 * @author Alexander Knueppel
 */
public class EliminateConstraintsPage extends AbstractWizardPage {

	private static final String METHOD_LABEL = "Refactoring Method:";
	private static final String METHOD_TOOLTIP = "Which method to use when refactoring to a product-equivalent model without complex constraints.";

	private static final String COMBO_CNF_LABEL = "Conjunctive Normal Form (CNF)";
	private static final String COMBO_NNF_LABEL = "Negation Normal Form (NNF)";
	private static final String COMBO_COMB_LABEL = "Combined Method";

	private static final String PRESERVE_CONFIGS_LABEL = "Preserve configurations:";
	private static final String PRESERVE_CONFIGS_TOOLTIP =
		"Whether to preserve the exact number of configurations. May result in large number of additional features and constraints.";

	private static final String REDUNDANT_LABEL = "Remove redundant constraints before conversion:";
	private static final String REDUNDANT_TOOLTIP =
		"Whether to remove redundant and tautological constraints before conversion. Requires SAT-analysis and " + "and can therefore be time consuming.";

	private final IFile inputModelFile;
	private Combo methodCombo;

	private final boolean trivial;
	private final String fileExtension;

	protected Text fileName;
	protected String path;
	protected ConversionMethod selectedMethod;
	protected boolean preserveConfigurations = false;
	protected boolean removeRedundancy = false;
	protected Combo fromFormatCombo;
	protected Combo toFormatCombo;

	/**
	 * @param name
	 */
	protected EliminateConstraintsPage(IFile file, String name, boolean trivial, String fileExtension) {
		super(name);
		// TODO Auto-generated constructor stub
		inputModelFile = file;
		this.trivial = trivial;
		this.fileExtension = fileExtension;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.dialogs.IDialogPage#createControl(org.eclipse.swt.widgets.Composite)
	 */
	@Override
	public void createControl(Composite parent) {
		final Composite composite = new Composite(parent, SWT.NULL);
		final GridLayout layout = new GridLayout(2, false);
		layout.verticalSpacing = 9;
		composite.setLayout(layout);

		final Label labelGenerate = new Label(composite, SWT.NULL);
		labelGenerate.setText(METHOD_LABEL);
		labelGenerate.setToolTipText(METHOD_TOOLTIP);

		methodCombo = new Combo(composite, SWT.BORDER | SWT.SINGLE | SWT.READ_ONLY);
		methodCombo.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		methodCombo.add(COMBO_COMB_LABEL);
		methodCombo.add(COMBO_NNF_LABEL);
		methodCombo.add(COMBO_CNF_LABEL);
		methodCombo.setText(COMBO_COMB_LABEL);
		selectedMethod = ConversionMethod.COMBINED;

		if (trivial) {
			methodCombo.setEnabled(false);
		}

		final Label fileNameLabel = new Label(composite, SWT.NULL);
		fileNameLabel.setText("File name:");

		final Composite fileComposite = new Composite(composite, SWT.NULL);
		fileComposite.setLayout(new GridLayout(2, false));
		fileComposite.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));

		if (inputModelFile != null) {
			fileName = new Text(fileComposite, SWT.BORDER | SWT.SINGLE);
			final String modelName = inputModelFile.getLocation().removeFileExtension().toOSString();
			fileName.setText(modelName + "-simple-constraints." + fileExtension);
			path = fileName.getText();
			fileName.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, true));
			final Button browseButton = new Button(fileComposite, SWT.NONE);
			browseButton.setText("Browse...");

			browseButton.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {

				@Override
				public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
					final String selectedPath = openFileDialog();
					if (selectedPath != null) {
						fileName.setText(selectedPath);
						final IPath path = new Path(selectedPath);
						if (path.getFileExtension() == null) {
							fileName.setText(selectedPath + "." + fileExtension);
						}
					}
				}
			});
		}

		final Label preserveConfigsLabel = new Label(composite, SWT.NULL);
		preserveConfigsLabel.setText(PRESERVE_CONFIGS_LABEL);
		preserveConfigsLabel.setToolTipText(PRESERVE_CONFIGS_TOOLTIP);
		final Button preserveConfigsButton = new Button(composite, SWT.CHECK);
		preserveConfigsButton.setToolTipText(PRESERVE_CONFIGS_TOOLTIP);
		preserveConfigsButton.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));

		final Label redundantLabel = new Label(composite, SWT.NULL);
		redundantLabel.setText(REDUNDANT_LABEL);
		redundantLabel.setToolTipText(REDUNDANT_TOOLTIP);
		final Button redundantButton = new Button(composite, SWT.CHECK);
		redundantButton.setToolTipText(REDUNDANT_TOOLTIP);
		redundantButton.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));

		if (trivial) {
			preserveConfigsButton.setEnabled(false);
		}

		// Add listeners
		methodCombo.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {
				final ConversionMethod[] methods = new ConversionMethod[] { ConversionMethod.COMBINED, ConversionMethod.NNF, ConversionMethod.CNF };
				final int selection = methodCombo.getSelectionIndex();
				selectedMethod = methods[selection];
				final boolean useCNF = selection < 2;
				preserveConfigsButton.setEnabled(true);
				preserveConfigsLabel.setEnabled(true);
			}
		});

		fileName.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {
				if (checkFileName()) {
					path = fileName.getText();
				}
			}
		});

		preserveConfigsButton.addSelectionListener(new SelectionListener() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				preserveConfigurations = preserveConfigsButton.getSelection();
				removeRedundancy = redundantButton.getSelection();
			}

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {}
		});

		redundantButton.addSelectionListener(new SelectionListener() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				removeRedundancy = redundantButton.getSelection();
			}

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {}
		});

		setControl(composite);
		checkFileName();
	}

	protected boolean checkFileName() {
		final String text = fileName.getText();
		final IPath path = new Path(text);
		if (path.isEmpty()) {
			updateErrorMessage("File name must be specified.");
			return false;
		}
		if (!path.isValidPath(text)) {
			updateErrorMessage(text + " is no valid path.");
			return false;
		}
		final String fileExtension = path.getFileExtension();
		if ((fileExtension == null) || !fileExtension.equals(fileExtension)) {
			updateErrorMessage("Exported model file must have " + fileExtension + " as file extension.");
			return false;
		}
//		if (path.toFile().exists()) {
//			updateStatusMessage("Selected file already exists. File will be overwritten.");
//			return false;
//		}
		updateErrorMessage(null);
		// updateStatusMessage(null);

		return true;
	}

	private void updateErrorMessage(String message) {
		setErrorMessage(message);
		setPageComplete(message == null);
	}

//	private void updateStatusMessage(String message) {
//		setMessage(message);
//		setPageComplete(true);
//	}

	private String openFileDialog() {
		final FileDialog fileDialog = new FileDialog(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell(), SWT.MULTI);

		fileDialog.setFileName("simple-constraints.xml");
		fileDialog.setFilterExtensions(new String[] { "*." + fileExtension });
		fileDialog.setOverwrite(true);
		fileDialog.setFilterPath(inputModelFile.getProject().getLocation().toOSString());
		return fileDialog.open();
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.wizards.AbstractWizardPage#putData()
	 */
	@Override
	protected void putData() {
		// TODO Auto-generated method stub

	}

}
