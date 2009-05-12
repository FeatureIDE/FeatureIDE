/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
package featureide.core.properties;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.dialogs.PropertyPage;

import featureide.core.CorePlugin;

/**
 * This class adds a property page to the properties dialog of a project. It is
 * responsible for changing the nature and the builder of a chosen project.
 * 
 * TODO Tom: the nature IDs should be read from the plugins
 * 
 * @author Janet Feigenspan
 */
public class FeatureIDENatureProperty extends PropertyPage {

	/**
	 * ComboBox for the selection of the nature
	 */
	private Combo natureSelection;

	private static final String AHEAD_NATURE = CorePlugin.PLUGIN_ID + ".jaknature";
	private static final String AHEAD_NATURE_COMBO_ENTRY = "Ahead";

	private static final String FEATURE_CPP_NATURE = CorePlugin.PLUGIN_ID + ".featureCPPNature";
	private static final String FEATURE_CPP_NATURE_COMBO_ENTRY = "Feature C++";

	private static final String FEATURE_HOUSE_NATURE = CorePlugin.PLUGIN_ID + ".featureHouseNature";
	private static final String FEATURE_HOUSE_NATURE_COMBO_ENTRY = "Feature House";

	/**
	 * the selected natures
	 */
	private String[] selectedNature;

	/**
	 * uses for saving the nature of the project
	 */
	private String[] previousNature;

	/**
	 * Constructor for SamplePropertyPage.
	 */
	public FeatureIDENatureProperty() {
		super();
	}

	/**
	 * @see PreferencePage#createContents(Composite)
	 */
	protected Control createContents(Composite parent) {
		Composite composite = new Composite(parent, SWT.NONE);
		GridLayout layout = new GridLayout();
		composite.setLayout(layout);
		GridData data = new GridData(GridData.FILL);
		data.grabExcessHorizontalSpace = true;
		composite.setLayoutData(data);

		addNatureSelection(composite);

		return composite;
	}

	/**
	 * adds the combobox and the according label for the selection of the
	 * natures to the properties page
	 * 
	 * @param composite
	 */
	private void addNatureSelection(Composite composite) {
		Label pathLabel = new Label(composite, SWT.NONE);
		pathLabel.setText("Choose a nature for Project " + getProjectName());

		natureSelection = new Combo(composite, SWT.READ_ONLY);

//		setFeatureProjectNature();

		natureSelection.add(AHEAD_NATURE_COMBO_ENTRY);
		natureSelection.add(FEATURE_CPP_NATURE_COMBO_ENTRY);
		natureSelection.add(FEATURE_HOUSE_NATURE_COMBO_ENTRY);

//		for (int i = 0; i < featureProjectNatureName.length; i++) {
//			natureSelection.add(featureProjectNatureName[i]);
//		}

		// get the nature that is set for the project and set it as selected
		// entry in the combobox
		previousNature = getNatureFromProjectFile();
		for (int i = 0; i < previousNature.length; i++) {
			if (previousNature[i].equals(AHEAD_NATURE)) {
				natureSelection.select(natureSelection
						.indexOf(AHEAD_NATURE_COMBO_ENTRY));
				setNature(new String[] { AHEAD_NATURE });
				break;
			}
			if (previousNature[i].equals(FEATURE_CPP_NATURE)) {
				natureSelection.select(natureSelection
						.indexOf(FEATURE_CPP_NATURE_COMBO_ENTRY));
				setNature(new String[] { FEATURE_CPP_NATURE });
				break;
			}
			if (previousNature[i].equals(FEATURE_HOUSE_NATURE)) {
				natureSelection.select(natureSelection
						.indexOf(FEATURE_HOUSE_NATURE_COMBO_ENTRY));
				setNature(new String[] { FEATURE_HOUSE_NATURE });
				break;
			}

//			for (int j = 0; j < featureProjectNatureID.length; j++) {
//				natureSelection.select(natureSelection
//						.indexOf(featureProjectNatureName[j]));
//				if (previousNature[i].equals(featureProjectNatureID[j]))
//					setNature(new String[] { featureProjectNatureID[j] });
//				break;
//			}
			natureSelection.select(0);
			setNature(new String[] { AHEAD_NATURE });
		}

		// register listener for the selection of an entry in the combobox
		natureSelection.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {
			}

			public void widgetSelected(SelectionEvent e) {
				String nature = natureSelection.getText();
//				for (int i = 0; i < featureProjectNatureName.length; i++) {
					if (nature.equals(AHEAD_NATURE_COMBO_ENTRY))
						setNature(new String[] { AHEAD_NATURE });
					else {
						if (nature.equals(FEATURE_HOUSE_NATURE_COMBO_ENTRY))
							setNature(new String [] {FEATURE_HOUSE_NATURE});
						else if (natureSelection.getText().equals(
								FEATURE_CPP_NATURE_COMBO_ENTRY))
							setNature(new String[] { FEATURE_CPP_NATURE });
					}
//				}
			}
		});
	}

	/**
	 * Gets the name of the project
	 * 
	 * @return the name of the project
	 */
	public String getProjectName() {
		String file = ((IResource) getElement()).getName().toString();
		return file;
	}

	/**
	 * Sets the nature of the project file to the selected nature, when Ok is
	 * pressed
	 */
	public boolean performOk() {
		setNatureInProjectFile();
		return true;
	}

	/**
	 * Sets the nature of the project file to the selected nature, when apply is
	 * pressed
	 */
	public void performApply() {
		performOk();
	}

	/**
	 * Sets the nature of the project to the original nature of the project,
	 * when cancel is pressed
	 */
	public boolean performCancel() {
		setNature(previousNature);
		setNatureInProjectFile();
		return true;
	}

	/**
	 * Sets the nature in the .project file of the current project Is called,
	 * when the "OK"-Button of the property page is clicked
	 */
	private void setNatureInProjectFile() {
		String project = getProjectName();
		IProject workspace = ResourcesPlugin.getWorkspace().getRoot()
				.getProject(project);
		try {
			IProjectDescription description = workspace.getDescription();
			description.setNatureIds(selectedNature);
			workspace.setDescription(description, null);
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}

	/**
	 * Gets the nature from the .project file of the current project
	 * 
	 * @return returns an array of all natures set for the current project
	 */
	private String[] getNatureFromProjectFile() {
		String project = getProjectName();
		IProject workspace = ResourcesPlugin.getWorkspace().getRoot()
				.getProject(project);
		try {
			IProjectDescription description = workspace.getDescription();
			previousNature = description.getNatureIds();
			return previousNature;
		} catch (CoreException e) {
			e.printStackTrace();
		}
		return null;
	}

	/**
	 * sets the selected natures
	 */
	public void setNature(String[] nature) {
		this.selectedNature = nature;
	}
	
}
