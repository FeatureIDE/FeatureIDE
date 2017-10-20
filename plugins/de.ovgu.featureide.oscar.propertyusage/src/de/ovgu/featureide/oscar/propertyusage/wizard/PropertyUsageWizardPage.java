package de.ovgu.featureide.oscar.propertyusage.wizard;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.dialogs.ContainerSelectionDialog;

public class PropertyUsageWizardPage extends WizardPage {

	private Text properties_path;
	private Button debug;
	private Combo output_format;
	private IContainer root = ResourcesPlugin.getWorkspace().getRoot();
	private IPath src_oscar_path;
	

	/**
	 * Create the wizard.
	 */
	public PropertyUsageWizardPage() {
		super("PropertyUsageWizardPage");
		setTitle("Property Usage Wizard");
		setDescription("Property Usage Extraction for Oscar.");
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
		src_oscar_path_t.setText(Platform.getLocation().toOSString());
			
		
		Button src_file_button = new Button(container, SWT.NONE);
		src_file_button.setBounds(453, 41, 94, 28);
		src_file_button.setText("Browse...");
		src_file_button.addSelectionListener(new SelectionAdapter() {
            public void widgetSelected(SelectionEvent e) {
            	ContainerSelectionDialog dialog = new ContainerSelectionDialog(getShell(), root, true, "Select a project:");
        		dialog.open();
        		src_oscar_path=root.getLocation().append(((IPath) (dialog.getResult())[0]));
        		src_oscar_path_t.setText(src_oscar_path.toOSString());
            }
            });
		
		Label lblPropertiesFile = new Label(container, SWT.NONE);
		lblPropertiesFile.setBounds(31, 78, 112, 14);
		lblPropertiesFile.setText("Properties file:");
		
		properties_path = new Text(container, SWT.BORDER);
		properties_path.setBounds(123, 75, 324, 19);
		
		Button prop_file_button = new Button(container, SWT.NONE);
		prop_file_button.setText("Browse...");
		prop_file_button.setBounds(453, 70, 94, 28);
		prop_file_button.addSelectionListener(new SelectionAdapter() {
            public void widgetSelected(SelectionEvent e) {
            	FileDialog dialog = new FileDialog(getShell(), SWT.OPEN);
        		dialog.setFilterPath(src_oscar_path != null ? src_oscar_path.toOSString() : root.getLocation().toOSString());
        		dialog.setFilterExtensions(new String [] {"*.properties"});
        		String result = dialog.open();
        		properties_path.setText(result);
            }
        });
		
		Label lblOutputFormat = new Label(container, SWT.NONE);
		lblOutputFormat.setBounds(31, 108, 82, 14);
		lblOutputFormat.setText("Output format:");
		
		output_format = new Combo(container, SWT.NONE);
		output_format.setItems(new String[] {"csv", "txt", "FeatureIDE model"});
		output_format.setBounds(125, 104, 324, 36);
		output_format.select(0);
		
		debug = new Button(container, SWT.CHECK);
		debug.setBounds(31, 161, 112, 18);
		debug.setText("Debug mode");
		container.setTabList(new Control[]{src_oscar_path_t, lblNewLabel, properties_path, lblPropertiesFile, output_format});
	}

	public IPath getSrc_oscar_path() {
		return src_oscar_path;
	}

	public String getProperties_path() {
		return properties_path.getText();
	}

	public boolean getDebug() {
		return debug.getSelection();
	}

	public String getOutput_format() {
		return output_format.getText();
	}

	
}
