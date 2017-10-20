package de.ovgu.featureide.oscar.propertyusage.wizard;

import org.eclipse.jface.wizard.Wizard;

import de.ovgu.featureide.oscar.propertyusage.core.PropertyUsage;

public class PropertyUsageWizard extends Wizard {
	
	private PropertyUsageWizardPage page;

	public PropertyUsageWizard() {
		setWindowTitle("New Wizard");
	}

	@Override
	public void addPages() {
		page = new PropertyUsageWizardPage();
		addPage(page);
	}

	@Override
	public boolean performFinish() {
		
		try{
			(new PropertyUsage()).findProject(page.getDebug(),page.getSrc_oscar_path(),page.getProperties_path(),page.getOutput_format());
			return true;
		}catch (Exception e){
			return false;
		}
		
	}

}
