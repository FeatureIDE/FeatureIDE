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
package de.ovgu.featureide.ui.ahead.properties;

import org.eclipse.core.resources.IResource;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.DirectoryDialog;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.List;
import org.eclipse.ui.dialogs.PropertyPage;

import de.ovgu.featureide.ahead.AheadComposer;
import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;

/**
 * The BuildPathPropertyPage class offers an interface to edit the class path which is used by the
 * JAVA compiler.
 * 
 * @author Tom Brosch
 */
public class BuildPathPropertyPage extends PropertyPage {

	private FileDialog fd;
	private DirectoryDialog dd;
	private List list;
	
	/**
	 * Constructor for SamplePropertyPage.
	 */
	public BuildPathPropertyPage() {
		super();
	}

	/**
	 * @see PreferencePage#createContents(Composite)
	 */
	protected Control createContents(Composite parent) {
		Composite composite = new Composite(parent, SWT.NONE);
		GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		composite.setLayout(layout);
		GridData data = new GridData(GridData.FILL);
		data.grabExcessHorizontalSpace = true;
		composite.setLayoutData(data);
		
		boolean rightComposer = false;
		IFeatureProject project = CorePlugin.getFeatureProject((IResource)getElement());
		if (project != null && project.getComposerID().equals(AheadComposer.COMPOSER_ID)) {
			rightComposer = true;
		}
		
		composite.setEnabled(rightComposer);
		
		fd = new FileDialog(getShell(), SWT.OPEN | SWT.MULTI);
		fd.setText("JAR Selection");
		fd.setFilterPath(null);
		fd.setFilterExtensions(new String[] { "*.jar; *.zip", "*.*" });
		
		dd = new DirectoryDialog(getShell());
		dd.setText("External Class Folder Selection");
		dd.setFilterPath(null);
		
		Label testLabel = new Label(composite, SWT.NONE);
		GridData data2 = new GridData();
		data2.horizontalSpan = 2;
		if (rightComposer)
			testLabel.setText("JARs and class folders on the build path:");
		else
			testLabel.setText("All options only applicable for feature projects in conjunction with the AHEAD composer.");
		testLabel.setLayoutData(data2);
		testLabel.setEnabled(rightComposer);
		
		list = new List(composite, SWT.MULTI | SWT.BORDER | SWT.H_SCROLL | SWT.V_SCROLL);
		GridData gd = new GridData(GridData.FILL_BOTH);
		gd.verticalSpan = 4;
		list.setLayoutData(gd);
		list.setEnabled(rightComposer);
		
		GridData hfill = new GridData(GridData.VERTICAL_ALIGN_BEGINNING);
		hfill.widthHint = 160;
		
		Button addJarBtn = new Button(composite, SWT.PUSH);
		addJarBtn.setText("Add External JARs...");
		addJarBtn.setLayoutData(hfill);
		addJarBtn.addSelectionListener(new SelectionListener() {
			
			public void widgetSelected(SelectionEvent e) {
				if (fd.open() != null)
					for (String filename : fd.getFileNames())
						list.add(fd.getFilterPath() + System.getProperty("file.separator") + filename);
			}
			
			public void widgetDefaultSelected(SelectionEvent e) {
			}
		});
		addJarBtn.setEnabled(rightComposer);
		
		Button addFolderBtn = new Button(composite, SWT.PUSH);
		addFolderBtn.setText("Add External Class Folder...");
		addFolderBtn.setLayoutData(hfill);
		addFolderBtn.addSelectionListener(new SelectionListener() {
			public void widgetSelected(SelectionEvent e) {
				String directory = dd.open();
				if (directory != null)
					list.add(directory);
			}
			
			public void widgetDefaultSelected(SelectionEvent e) {
			}
		});
		addFolderBtn.setEnabled(rightComposer);
		
		//Button editBtn = new Button(composite, SWT.PUSH);
		//editBtn.setText("Edit...");
		//editBtn.setLayoutData(hfill);
		
		Button removeBtn = new Button(composite, SWT.PUSH);
		removeBtn.setText("Remove");
		removeBtn.setLayoutData(hfill);
		removeBtn.addSelectionListener(new SelectionListener() {
			
			public void widgetSelected(SelectionEvent e) {
				list.remove(list.getSelectionIndices());
			}
			
			public void widgetDefaultSelected(SelectionEvent e) {
			}
		});
		removeBtn.setEnabled(rightComposer);
		
		performDefaults();
		
		return composite;
	}

	protected void performDefaults() {
		// Populate the owner text field with the default value
		list.removeAll();
		
		IFeatureProject project = CorePlugin.getFeatureProject((IResource)getElement());
		if (project != null) {
			String[] classPath = project.getAdditionalJavaClassPath();
			for (String str : classPath)
				list.add(str);
		}
	}
	
	public boolean performOk() {
		IFeatureProject project = CorePlugin.getFeatureProject((IResource)getElement());
		if (project != null)
			project.setAdditionalJavaClassPath(list.getItems());
		
		return true;
	}

}
