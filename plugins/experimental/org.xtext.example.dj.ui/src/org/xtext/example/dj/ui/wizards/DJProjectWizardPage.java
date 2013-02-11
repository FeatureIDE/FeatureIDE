package org.xtext.example.dj.ui.wizards;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.dialogs.ContainerSelectionDialog;

import ProjectGeneration.ProjectGenerationFactory;
import ProjectGeneration.ProjectSettings;
import ProjectGeneration.SampleSet;

/**
 * The "New" wizard page allows setting the container for the new file as well
 * as the file name. The page will only accept file name without the extension
 * OR with the extension that matches the expected one (swrtj).
 */

public class DJProjectWizardPage extends WizardPage {
	private Text containerText;
	private Combo sampleSet;
	private ISelection selection;
	private boolean sampleSetChoice;
	
	/**
	 * Constructor for SampleNewWizardPage.
	 * 
	 * @param pageName
	 * @param sampleSetChoice
	 */
	public DJProjectWizardPage(ISelection selection, boolean sampleSetChoice) {
		super("wizardPage");
		setTitle("Multi-page Editor File");
		setDescription("This wizard creates a new DeltaJ PROJECT.");
		this.selection = selection;
		this.sampleSetChoice = sampleSetChoice;
	}

	/**
	 * @see IDialogPage#createControl(Composite)
	 */
	public void createControl(Composite parent) {
		Composite container = new Composite(parent, SWT.NULL);
		GridLayout layout = new GridLayout();
		container.setLayout(layout);
		layout.numColumns = 3;
		layout.verticalSpacing = 9;
		Label label = new Label(container, SWT.NULL);
		label.setText("&Project name:");

		containerText = new Text(container, SWT.BORDER | SWT.SINGLE);
		containerText.setText("NewDJProject");
		int counter = 1;
		while(exists(containerText.getText())) {
			containerText.setText("NewDJProject" + counter);
			counter++;
		}
		
		GridData gd = new GridData(GridData.FILL_HORIZONTAL);
		containerText.setLayoutData(gd);
		containerText.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				dialogChanged();
			}
		});

		Button button = new Button(container, SWT.PUSH);
		button.setText("Browse...");
		button.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {
				handleBrowse();
			}
		});
		
		if(sampleSetChoice) {
			Label sampleSetLabel = new Label(container, SWT.NULL);
			sampleSetLabel.setText("&Initial sample:");		
			sampleSet = new Combo(container, SWT.BORDER | SWT.READ_ONLY);
		}
		
		initialize();
		dialogChanged();
		setControl(container);
	}

	/**
	 * Tests if the current workbench selection is a suitable container to use.
	 */
	@SuppressWarnings("unused")
	private void initialize() {
		if(sampleSetChoice) {
			int index = 0;
			
			for(SampleSet value : SampleSet.values()) {
				sampleSet.add(value.toString().toLowerCase(), index);
				index++;
			}
			
			if(index > 1) sampleSet.select(1);
			else sampleSet.select(0);
		}
		
		if (selection != null && selection.isEmpty() == false
				&& selection instanceof IStructuredSelection) {
			IStructuredSelection ssel = (IStructuredSelection) selection;
			if (ssel.size() > 1)
				return;
			Object obj = ssel.getFirstElement();
			if (obj instanceof IResource) {
				IContainer container;
				if (obj instanceof IContainer)
					container = (IContainer) obj;
				else
					container = ((IResource) obj).getParent();
			}
		}
	}

	/**
	 * Uses the standard container selection dialog to choose the new value for
	 * the container field.
	 */

	private void handleBrowse() {
		ContainerSelectionDialog dialog = new ContainerSelectionDialog(
				getShell(), ResourcesPlugin.getWorkspace().getRoot(), false,
				"Select new file container");
		if (dialog.open() == ContainerSelectionDialog.OK) {
			Object[] result = dialog.getResult();
			if (result.length == 1) {
				containerText.setText(((Path) result[0]).toString());
			}
		}
	}

	/**
	 * Ensures that both text fields are set.
	 */
	private void dialogChanged() {
		IResource container = ResourcesPlugin.getWorkspace().getRoot()
				.findMember(new Path(getContainerName()));

		if (getContainerName().length() == 1) {
			updateStatus("Project name must be specified");
			return;
		}
		if (container != null
				&& (container.getType() & (IResource.PROJECT | IResource.FOLDER)) != 0) {
			updateStatus("The project name refers to an existing project");
			return;
		}
		if (container != null && !container.isAccessible()) {
			updateStatus("Project must be writable");
			return;
		}
		updateStatus(null);
	}

	private void updateStatus(String message) {
		setErrorMessage(message);
		setPageComplete(message == null);
	}

	public String getContainerName() {
		return containerText.getText() + "/";
	}
	
	public ProjectSettings getSettings() {
		ProjectSettings settings = ProjectGenerationFactory.eINSTANCE.createProjectSettings();
		settings.setName(normalize(containerText.getText()));
		if (sampleSet != null)
			settings.setSampleSet(SampleSet.get(sampleSet.getSelectionIndex()));
		else
			settings.setSampleSet(SampleSet.EMPTY);
		
		return settings;
	}
	
	/* Service methods */
	
	private boolean exists(String projectName) {
		IResource container = ResourcesPlugin.getWorkspace().getRoot()
		                      .findMember(projectName);
		
		return (container != null && 
			   (container.getType() & (IResource.PROJECT | IResource.FOLDER)) != 0);
	}
	
	public static String normalize(String name) {
		String normalized = "";
		
		for(char ch : name.toCharArray()) {
			if((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z')) {
				normalized += ch;
			}	
		}
		
		return normalized;
	}
}