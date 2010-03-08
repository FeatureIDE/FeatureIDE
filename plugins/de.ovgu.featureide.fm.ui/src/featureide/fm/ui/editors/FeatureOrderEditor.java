/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package featureide.fm.ui.editors;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.Collection;
import java.util.Scanner;
import java.util.ArrayList;

import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.SWT;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorPart;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Label;

import featureide.fm.core.Feature;
import featureide.fm.core.FeatureModel;

/**
 * Additional editor page for the feature model editor. In this editor the order
 * of the features can be change
 * 
 * @author Christian Becker
 */
public class FeatureOrderEditor extends EditorPart {

	public static final String ID = "featureide.fm.ui.editors.FeatureOrderEditor";

	private List featurelist = null;

	private Button up = null;

	private Button down = null;

	private Button activate = null;

	private IEditorInput input;

	private IEditorSite site;

	private Writer fw;

	private boolean dirty = false;
	
	private FeatureModel featureModel;

	public FeatureOrderEditor(FeatureModel feature) {
		featureModel = feature;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @seeorg.eclipse.ui.part.EditorPart#doSave(org.eclipse.core.runtime.
	 * IProgressMonitor)
	 */
	@Override
	public void doSave(IProgressMonitor monitor) {

		writeFeaturestoOrderFile();
		dirty = false;
		firePropertyChange(IEditorPart.PROP_DIRTY);
	}

	public IEditorSite getSite() {
		return site;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.part.EditorPart#doSaveAs()
	 */
	@Override
	public void doSaveAs() {
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.part.EditorPart#init(org.eclipse.ui.IEditorSite,
	 * org.eclipse.ui.IEditorInput)
	 */
	@Override
	public void init(IEditorSite site, IEditorInput input)
			throws PartInitException {
		this.input = input;
		this.site = site;

	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.part.EditorPart#isSaveAsAllowed()
	 */
	@Override
	public boolean isSaveAsAllowed() {
		return false;
	}

	public void initOrderEditor(){
		ArrayList<String> list = readFeaturesfromOrderFile();
		if (list == null) {
			activate.setSelection(false);
			enableUI(false);
			for (Feature ft : featureModel.getFeatures()) {
				if (ft.isLayer())
					featurelist.add(ft.getName());
				
			}
			writeFeaturestoOrderFile();
		} else {
			activate.setSelection(true);
			enableUI(true);
			for (String str : list) {
				featurelist.add(str);
			}
		}
		
		
	}
	
	public void updateOrderEditor(Collection<Feature> features) {
		featurelist.removeAll();
		
		for (Feature ft : features) {
			if (ft.isLayer())
				featurelist.add(ft.getName());
			
		}
		writeFeaturestoOrderFile();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.ui.part.WorkbenchPart#createPartControl(org.eclipse.swt.widgets
	 * .Composite)
	 */
	@Override
	public void createPartControl(Composite parent) {
		GridData gridData;
		GridLayout layout = new GridLayout();
		layout.numColumns = 3;
		Composite comp = new Composite(parent, SWT.NONE);
		comp.setLayout(layout);

		Label label1 = new Label(comp, SWT.NONE);
		label1.setText("User-defined feature order");

		activate = new Button(comp, SWT.CHECK);
		activate
				.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
					public void widgetSelected(
							org.eclipse.swt.events.SelectionEvent e) {
						boolean selection = activate.getSelection();
						enableUI(selection);
						dirty = true;
						firePropertyChange(EditorPart.PROP_DIRTY);
					}
				});

		featurelist = new List(comp, SWT.NONE | SWT.BORDER | SWT.V_SCROLL);
		gridData = new GridData(GridData.FILL_BOTH);
		gridData.horizontalSpan = 2;
		gridData.grabExcessHorizontalSpace = true;
		gridData.verticalSpan = 3;
		gridData.grabExcessVerticalSpace = true;
		featurelist.setLayoutData(gridData);
		featurelist.setEnabled(false);

		gridData = new GridData(GridData.HORIZONTAL_ALIGN_END);
		gridData.widthHint = 70;
		up = new Button(comp, SWT.NONE);
		up.setText("Up");
		up.setLayoutData(gridData);
		up.setEnabled(false);
		up.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
				int focus = featurelist.getFocusIndex();
				if (focus != 0) { // First Element is selected, no change
					String temp = featurelist.getItem(focus - 1);
					featurelist.setItem(focus - 1, featurelist.getItem(focus));
					featurelist.setItem(focus, temp);
					featurelist.setSelection(focus - 1);
					dirty = true;
					firePropertyChange(EditorPart.PROP_DIRTY);

				}
			}
		});
		;
		down = new Button(comp, SWT.NONE);
		down.setText("Down");
		down.setLayoutData(gridData);
		down.setEnabled(false);
		down
				.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
					public void widgetSelected(
							org.eclipse.swt.events.SelectionEvent e) {
						int focus = featurelist.getFocusIndex();
						if (focus != featurelist.getItemCount() - 1) { // Last
																		// Element
																		// is
																		// selected,
																		// no
																		// change
							String temp = featurelist.getItem(focus + 1);
							featurelist.setItem(focus + 1, featurelist
									.getItem(focus));
							featurelist.setItem(focus, temp);
							featurelist.setSelection(focus + 1);
							dirty = true;
							firePropertyChange(PROP_DIRTY);

						}
					}
					// }
				});
	}

	/**
	 * Write the order of the features in the .order file in the feature project
	 * directory
	 */

	public void writeFeaturestoOrderFile() {

		File file = ((IFile) input.getAdapter(IFile.class)).getProject()
				.getLocation().toFile();
		String newLine = System.getProperty("line.separator");
		try {
			fw = new FileWriter(file.toString() + System.getProperty("file.separator") + ".order");
			if (activate.getSelection())
				fw.write("true" + newLine);
			else
				fw.write("false" + newLine);
			for (int i = 0; i < featurelist.getItemCount(); i++) {
				fw.write(featurelist.getItem(i));
				fw.append(System.getProperty("line.separator"));
			}
			fw.close();
		} catch (IOException e) {

			e.printStackTrace();
		}
	}
/*
	public void featureOrderReader() {
		File file = ((IFile) input.getAdapter(IFile.class)).getProject()
				.getLocation().toFile();
		file = new File(file.toString() + "\\.order");
		featurelist.removeAll();
		Scanner scanner = null;
		try {
			scanner = new Scanner(file);
		} catch (FileNotFoundException e) {

			e.printStackTrace();
		}
		while (scanner.hasNext()) {
			featurelist.add(scanner.next());
		}
	}*/
/**
 * 
 * @return Return the FeatureOrder as an ArrayList. Return null if the "userdefined-order" is deactivate or if no order file exists.
 * In this case the method will create a new file. 
 */
	public ArrayList<String> readFeaturesfromOrderFile() {
		if (((IFile) input.getAdapter(IFile.class)).getProject() == null)
			return null;  //Avoids NPE when project and its contents are deleted and .order file is still open
		File file = ((IFile) input.getAdapter(IFile.class)).getProject().getLocation().toFile();
		ArrayList<String> list;
		Scanner scanner = null;
		String fileSep = System.getProperty("file.separator");
		file = new File(file.toString()+ fileSep + ".order");
		if (file.exists()){
			try {
				scanner = new Scanner(file);
			} catch (FileNotFoundException e) {
				System.out.println("Problem to open the order file");
				e.printStackTrace();
			}
			if (scanner.hasNext() && scanner.next().equals("true")) {
				list = new ArrayList<String>();
				while (scanner.hasNext()) {
					list.add(scanner.next());
				}
				return list;
			} else {
				return null;
			}
		}else {
			try {
				file.createNewFile();
			} catch (IOException e) {
				e.printStackTrace();
			}
			return null;
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.part.WorkbenchPart#setFocus()
	 */
	@Override
	public void setFocus() {

	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.part.EditorPart#isDirty()
	 */
	@Override
	public boolean isDirty() {
		return dirty;

	}

	/**
	 * @param selection
	 */
	private void enableUI(boolean selection) {
		featurelist.setEnabled(selection);
		up.setEnabled(selection);
		down.setEnabled(selection);
	}

}
