package de.ovgu.featureide.oscar.propertyusage.wizard;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jface.viewers.CheckStateChangedEvent;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.dialogs.ContainerSelectionDialog;
import org.eclipse.ui.dialogs.FilteredResourcesSelectionDialog;
import org.eclipse.ui.dialogs.ResourceListSelectionDialog;

import de.ovgu.featureide.oscar.IO.ExportImport;

public class PropertyUsageWizardPage extends WizardPage {

	private Button debug;
	private Combo output_format;
	private IContainer root = ResourcesPlugin.getWorkspace().getRoot();
	private IProject src_oscar_path;
	private IFile properties_path;
	

	/**
	 * Create the wizard.
	 */
	public PropertyUsageWizardPage() {
		super("PropertyUsageWizardPage");
		setTitle("Property Usage Wizard");
		setDescription("Property Usage Extraction for Oscar.");
		setPageComplete(false);
	}

	/**
	 * Create contents of the wizard.
	 * @param parent
	 */
	public void createControl(Composite parent) {
		Composite container = new Composite(parent, SWT.NULL);

		setControl(container);
		
		Label lblNewLabel = new Label(container, SWT.NONE);
		lblNewLabel.setBounds(31, 48, 136, 24);
		lblNewLabel.setText("Source code root folder:");
		
		Text src_oscar_path_t = new Text(container, SWT.BORDER);
		src_oscar_path_t.setBounds(173, 45, 274, 19);
		src_oscar_path_t.addModifyListener(new ModifyListener(){

			@Override
			public void modifyText(ModifyEvent e) {
				if (isPageComplete()){
					setPageComplete(true);
				}
				
			}
			
		});
			
		
		Button src_file_button = new Button(container, SWT.NONE);
		src_file_button.setBounds(453, 41, 94, 28);
		src_file_button.setText("Browse...");
		src_file_button.addSelectionListener(new SelectionAdapter() {
            public void widgetSelected(SelectionEvent e) {
            	ContainerSelectionDialog dialog = new ContainerSelectionDialog(getShell(), root, false, "Select a Project");
        		if (dialog.open() == ResourceListSelectionDialog.OK){
	        		IPath src_oscar_path_p= (IPath) dialog.getResult()[0];
	        		src_oscar_path_t.setText(src_oscar_path_p.lastSegment());
	        		src_oscar_path = ResourcesPlugin.getWorkspace().getRoot().getProject(src_oscar_path_p.toString());
        		}
            }
        });
		
		Label lblPropertiesFile = new Label(container, SWT.NONE);
		lblPropertiesFile.setBounds(31, 78, 112, 14);
		lblPropertiesFile.setText("Properties file:");
		
		Text properties_path_t = new Text(container, SWT.BORDER);
		properties_path_t.setBounds(123, 75, 324, 19);
		
		properties_path_t.addModifyListener(new ModifyListener(){

			@Override
			public void modifyText(ModifyEvent e) {
				if (isPageComplete()){
					setPageComplete(true);
				}
				
			}
			
		});
		
		Button prop_file_button = new Button(container, SWT.NONE);
		prop_file_button.setText("Browse...");
		prop_file_button.setBounds(453, 70, 94, 28);
		
		prop_file_button.addSelectionListener(new SelectionAdapter() {
            public void widgetSelected(SelectionEvent e) {
            	FilteredResourcesSelectionDialog dialog = new FilteredResourcesSelectionDialog(getShell(),false, src_oscar_path ,IResource.FILE);
            	dialog.setInitialPattern("*.properties");
        		if (dialog.open() == ResourceListSelectionDialog.OK){
	        		properties_path=(IFile)dialog.getResult()[0];
	        		properties_path_t.setText(properties_path.getName());
        		}
            }
        });
		
		Label lblOutputFormat = new Label(container, SWT.NONE);
		lblOutputFormat.setBounds(31, 108, 82, 14);
		lblOutputFormat.setText("Output format:");
		
		output_format = new Combo(container, SWT.READ_ONLY);
		output_format.setItems(new String[] {ExportImport.CSV, ExportImport.MOD, ExportImport.ALL});
		output_format.setBounds(125, 104, 324, 36);
		output_format.select(0);
		
		debug = new Button(container, SWT.CHECK);
		debug.setSelection(true);
		debug.setBounds(31, 161, 112, 18);
		debug.setText("Debug mode");
		container.setTabList(new Control[]{src_oscar_path_t, lblNewLabel, properties_path_t, lblPropertiesFile, output_format});
	}

	public IProject getSrc_oscar_path() {
		return src_oscar_path;
	}

	public IFile getProperties_path() {
		return properties_path;
	}

	public boolean getDebug() {
		return debug.getSelection();
	}

	public String getOutput_format() {
		return output_format.getText();
	}

	@Override
	public boolean isPageComplete() {
		return (src_oscar_path != null && properties_path !=null);
	}
	
	
	
	

	
}
