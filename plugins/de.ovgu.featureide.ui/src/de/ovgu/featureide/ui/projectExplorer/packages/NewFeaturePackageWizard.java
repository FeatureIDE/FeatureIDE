/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.projectExplorer.packages;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;

import de.ovgu.featureide.ui.UIPlugin;

/**
 * Creates a Java package in a feature folder, like the New Package wizard of JDT does in a source folder: the package <code>de.ovgu.example</code> is
 * created as the folders <code>de/ovgu/example</code>.
 *
 * @author Philipp Hehnle
 */
public class NewFeaturePackageWizard extends Wizard implements INewWizard {

	public static final String ID = UIPlugin.PLUGIN_ID + ".wizards.NewFeaturePackageWizard";

	private FeatureJavaLocation location;
	private NewFeaturePackagePage page;

	public NewFeaturePackageWizard() {
		setWindowTitle("New Java Package");
		setDefaultPageImageDescriptor(FeatureWizardSupport.getJdtWizardBanner("newpack_wiz.png"));
	}

	@Override
	public void init(IWorkbench workbench, IStructuredSelection selection) {
		location = FeatureWizardSupport.getLocation(selection);
	}

	@Override
	public void addPages() {
		page = new NewFeaturePackagePage(location);
		addPage(page);
	}

	@Override
	public boolean performFinish() {
		final String packageName = page.getPackageName();
		try {
			location.createPackage(packageName);
		} catch (final CoreException e) {
			UIPlugin.getDefault().logError(e);
			MessageDialog.openError(getShell(), getWindowTitle(), e.getMessage());
			return false;
		}
		FeatureWizardSupport.selectAndReveal(location.getPackageNode(packageName));
		return true;
	}

	private static final class NewFeaturePackagePage extends WizardPage {

		private final FeatureJavaLocation location;
		private Text nameText;

		NewFeaturePackagePage(FeatureJavaLocation location) {
			super("NewFeaturePackagePage");
			this.location = location;
			setTitle("Java Package");
			setDescription("Create a new Java package in a feature.");
		}

		@Override
		public void createControl(Composite parent) {
			final Composite composite = new Composite(parent, SWT.NONE);
			composite.setLayout(new GridLayout(2, false));

			new Label(composite, SWT.NONE).setText("Source folder:");
			final Text rootText = new Text(composite, SWT.BORDER | SWT.READ_ONLY);
			rootText.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
			rootText.setText((location != null) ? location.getRootLabel() : "");

			new Label(composite, SWT.NONE).setText("Name:");
			nameText = new Text(composite, SWT.BORDER);
			nameText.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
			if (location != null) {
				nameText.setText(location.getPackageName());
				nameText.setSelection(nameText.getText().length());
			}
			nameText.addModifyListener(e -> validate());

			setControl(composite);
			validate();
			// do not show an error before the user typed anything
			if (getPackageName().isEmpty() && (location != null)) {
				setErrorMessage(null);
			}
			nameText.setFocus();
		}

		String getPackageName() {
			return nameText.getText().trim();
		}

		private void validate() {
			final IStatus status;
			if (location == null) {
				status = new Status(IStatus.ERROR, UIPlugin.PLUGIN_ID, "Select a feature folder or a package in a feature folder.");
			} else {
				final IStatus nameStatus = FeatureJavaLocation.validatePackageName(getPackageName(), false);
				if ((nameStatus.getSeverity() != IStatus.ERROR) && location.getPackageFolder(getPackageName()).exists()) {
					status = new Status(IStatus.ERROR, UIPlugin.PLUGIN_ID, "Package already exists.");
				} else {
					status = nameStatus;
				}
			}
			setPageComplete(FeatureWizardSupport.showStatus(this, status));
		}
	}
}
