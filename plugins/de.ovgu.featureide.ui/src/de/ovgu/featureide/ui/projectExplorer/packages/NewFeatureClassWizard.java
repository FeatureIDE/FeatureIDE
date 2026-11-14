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

import java.io.ByteArrayInputStream;
import java.io.UnsupportedEncodingException;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ProjectScope;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.preferences.IScopeContext;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;

import de.ovgu.featureide.ui.UIPlugin;

/**
 * Creates a Java class (or interface, enum, record) in a package of a feature folder, like the New Class wizard of JDT does in a source folder: the file
 * contains the package declaration and the type declaration.
 *
 * @author Philipp Hehnle
 */
public class NewFeatureClassWizard extends Wizard implements INewWizard {

	public static final String ID = UIPlugin.PLUGIN_ID + ".wizards.NewFeatureClassWizard";

	/**
	 * The kinds of types the wizard can create.
	 */
	public enum Kind {
		CLASS("class"), INTERFACE("interface"), ENUM("enum"), RECORD("record");

		private final String keyword;

		Kind(String keyword) {
			this.keyword = keyword;
		}

		public String getKeyword() {
			return keyword;
		}
	}

	private FeatureJavaLocation location;
	private NewFeatureClassPage page;

	public NewFeatureClassWizard() {
		setWindowTitle("New Java Class");
		setDefaultPageImageDescriptor(FeatureWizardSupport.getJdtWizardBanner("newclass_wiz.png"));
	}

	@Override
	public void init(IWorkbench workbench, IStructuredSelection selection) {
		location = FeatureWizardSupport.getLocation(selection);
	}

	@Override
	public void addPages() {
		page = new NewFeatureClassPage(location);
		addPage(page);
	}

	@Override
	public boolean performFinish() {
		final String packageName = page.getPackageName();
		final String typeName = page.getTypeName();
		final IFile file;
		try {
			file = createType(location, packageName, typeName, page.getKind(), page.isCreateMain());
		} catch (final CoreException e) {
			UIPlugin.getDefault().logError(e);
			MessageDialog.openError(getShell(), getWindowTitle(), e.getMessage());
			return false;
		}
		FeatureWizardSupport.selectAndReveal(file);
		final IWorkbenchPage workbenchPage = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
		try {
			IDE.openEditor(workbenchPage, file, true);
		} catch (final PartInitException e) {
			UIPlugin.getDefault().logError(e);
		}
		return true;
	}

	/**
	 * Creates the package (if needed) and the source file of the type.
	 *
	 * @return the created file.
	 * @throws CoreException if the file already exists or cannot be created.
	 */
	public static IFile createType(FeatureJavaLocation location, String packageName, String typeName, Kind kind, boolean createMain) throws CoreException {
		final IContainer packageFolder = location.createPackage(packageName);
		final IFile file = packageFolder.getFile(new Path(typeName + ".java"));
		if (file.exists()) {
			throw new CoreException(new Status(IStatus.ERROR, UIPlugin.PLUGIN_ID, "Type already exists: " + file.getFullPath()));
		}
		final String source = createSource(packageName, typeName, kind, createMain, getLineSeparator(packageFolder));
		final String charset = packageFolder.getDefaultCharset();
		try {
			file.create(new ByteArrayInputStream(source.getBytes(charset)), true, null);
		} catch (final UnsupportedEncodingException e) {
			throw new CoreException(new Status(IStatus.ERROR, UIPlugin.PLUGIN_ID, e.getMessage(), e));
		}
		return file;
	}

	/**
	 * @return the source code of a new type with an empty body, preceded by the package declaration (unless the package is the default package).
	 */
	public static String createSource(String packageName, String typeName, Kind kind, boolean createMain, String nl) {
		final StringBuilder source = new StringBuilder();
		if (!packageName.isEmpty()) {
			source.append("package ").append(packageName).append(';').append(nl).append(nl);
		}
		source.append("public ").append(kind.getKeyword()).append(' ').append(typeName);
		if (kind == Kind.RECORD) {
			source.append("()");
		}
		source.append(" {").append(nl).append(nl);
		if (createMain && (kind == Kind.CLASS)) {
			source.append("\tpublic static void main(String[] args) {").append(nl).append(nl).append("\t}").append(nl).append(nl);
		}
		source.append('}').append(nl);
		return source.toString();
	}

	/**
	 * @return the line separator configured for the project or the workspace (Preferences &gt; General &gt; Workspace &gt; New text file line
	 *         delimiter).
	 */
	private static String getLineSeparator(IContainer container) {
		final IScopeContext[] scopes = { new ProjectScope(container.getProject()), InstanceScope.INSTANCE };
		return Platform.getPreferencesService().getString(Platform.PI_RUNTIME, Platform.PREF_LINE_SEPARATOR, System.lineSeparator(), scopes);
	}

	private static final class NewFeatureClassPage extends WizardPage {

		private final FeatureJavaLocation location;
		private Text packageText;
		private Text nameText;
		private Button mainButton;
		private Kind kind = Kind.CLASS;

		NewFeatureClassPage(FeatureJavaLocation location) {
			super("NewFeatureClassPage");
			this.location = location;
			setTitle("Java Class");
			setDescription("Create a new Java class in a feature.");
		}

		@Override
		public void createControl(Composite parent) {
			final Composite composite = new Composite(parent, SWT.NONE);
			composite.setLayout(new GridLayout(2, false));

			new Label(composite, SWT.NONE).setText("Source folder:");
			final Text rootText = new Text(composite, SWT.BORDER | SWT.READ_ONLY);
			rootText.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
			rootText.setText((location != null) ? location.getRootLabel() : "");

			new Label(composite, SWT.NONE).setText("Package:");
			packageText = new Text(composite, SWT.BORDER);
			packageText.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
			packageText.setText((location != null) ? location.getPackageName() : "");
			packageText.addModifyListener(e -> validate());

			new Label(composite, SWT.NONE).setText("Name:");
			nameText = new Text(composite, SWT.BORDER);
			nameText.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
			nameText.addModifyListener(e -> validate());

			new Label(composite, SWT.NONE).setText("Kind:");
			final Composite kinds = new Composite(composite, SWT.NONE);
			kinds.setLayout(new GridLayout(Kind.values().length, false));
			for (final Kind each : Kind.values()) {
				final Button button = new Button(kinds, SWT.RADIO);
				button.setText(each.getKeyword());
				button.setSelection(each == kind);
				button.addSelectionListener(new SelectionAdapter() {

					@Override
					public void widgetSelected(SelectionEvent e) {
						if (button.getSelection()) {
							kind = each;
							mainButton.setEnabled(kind == Kind.CLASS);
						}
					}
				});
			}

			new Label(composite, SWT.NONE);
			mainButton = new Button(composite, SWT.CHECK);
			mainButton.setText("public static void main(String[] args)");

			setControl(composite);
			validate();
			// do not show an error before the user typed a name
			setErrorMessage(null);
			nameText.setFocus();
		}

		String getPackageName() {
			return packageText.getText().trim();
		}

		String getTypeName() {
			return nameText.getText().trim();
		}

		Kind getKind() {
			return kind;
		}

		boolean isCreateMain() {
			return mainButton.getSelection() && (kind == Kind.CLASS);
		}

		private void validate() {
			IStatus status;
			if (location == null) {
				status = new Status(IStatus.ERROR, UIPlugin.PLUGIN_ID, "Select a feature folder or a package in a feature folder.");
			} else {
				status = FeatureJavaLocation.validatePackageName(getPackageName(), true);
				if (status.getSeverity() != IStatus.ERROR) {
					final IStatus nameStatus = FeatureJavaLocation.validateTypeName(getTypeName());
					if (nameStatus.getSeverity() == IStatus.ERROR) {
						status = nameStatus;
					} else if (location.getPackageFolder(getPackageName()).getFile(new Path(getTypeName() + ".java")).exists()) {
						status = new Status(IStatus.ERROR, UIPlugin.PLUGIN_ID, "Type already exists.");
					} else if (nameStatus.getSeverity() == IStatus.WARNING) {
						status = nameStatus;
					} else if (getPackageName().isEmpty()) {
						status = new Status(IStatus.WARNING, UIPlugin.PLUGIN_ID, "The use of the default package is discouraged.");
					}
				}
			}
			setPageComplete(FeatureWizardSupport.showStatus(this, status));
		}
	}
}
