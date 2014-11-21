package de.ovgu.featureide.ui.variantimport;

import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

public class SPLMigrationDialogNamePage extends WizardPage
{	
	protected GridData gridDataFill = new GridData(GridData.FILL_HORIZONTAL);

	private Text newProjectName;
	
	public SPLMigrationDialogNamePage()
	{
		super("Give a name for the Software Product Line");
		setTitle("Project Name");
		setDescription("Give a name for the Software Product Line");
	}

	@Override
	public void createControl(Composite parent)
	{
		Composite container = new Composite(parent, SWT.NONE);
		final GridLayout gridLayout = new GridLayout();
		
	    gridLayout.numColumns = 1;
	    container.setLayout(gridLayout);
	    setControl(container);
	    
	    gridLayout.numColumns = 2;
	    
	    Group nameGroup = new Group(container, SWT.NONE);
	    nameGroup.setLayout(gridLayout);
	    nameGroup.setLayoutData(gridDataFill);
	    
	    String tooltip = "Give a name for the new Software Product Line";
		
	    Label newProductNameLabel = new Label(nameGroup, SWT.NULL);
		newProductNameLabel.setText("&Project Name:");
		newProductNameLabel.setToolTipText(tooltip);
		
		newProjectName = new Text(nameGroup, SWT.BORDER | SWT.SINGLE);
		newProjectName.setLayoutData(gridDataFill);
		newProjectName.setText(DefaultSPLMigrator.DEFAULT_PROJECT_NAME);
		newProjectName.setToolTipText(tooltip);
		
		addNameChangeListener();
	}
	
	private void addNameChangeListener()
	{
		newProjectName.addModifyListener(new ModifyListener() {
			
			@Override
			public void modifyText(ModifyEvent e) {
				onNameChange();
			}
		});
			
	}

	protected void onNameChange()
	{
		if(ResourcesPlugin.getWorkspace().getRoot().getProject(getProjectName()).exists())
			setErrorMessage("A project with this name already exists in the workspace. Please change the name.");
		else
			setErrorMessage(null);
	}

	public String getProjectName() {
		return newProjectName.getText();
	}
	
	@Override
	public boolean isPageComplete()
	{
		if(isCurrentPage())
			return getErrorMessage() == null;
		else 
			return true;
	}
	
	@Override
	public boolean canFlipToNextPage()
	{
		return !(getProjectName() == null || getProjectName().isEmpty()) && isPageComplete();
	}
	
}
