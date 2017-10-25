package de.ovgu.featureide.oscar.propertyusage.wizard;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.oscar.IO.Console;
import de.ovgu.featureide.oscar.propertyusage.core.PropertyUsage;

public class PropertyUsageWizard extends Wizard {
	
	private PropertyUsageWizardPage page;
	private Console console=new Console();
	private IProject project;

	public PropertyUsageWizard() {
		setWindowTitle("New Wizard");
		IWorkbenchWindow window = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
	    
	    if (window != null)
	    {
	        IStructuredSelection selection = (IStructuredSelection) window.getSelectionService().getSelection();
	        Object firstElement = selection.getFirstElement();
	        if (firstElement instanceof IAdaptable)
	        {
	             project = (IProject)((IAdaptable)firstElement).getAdapter(IProject.class);

	        }
	    }
	
		
	}

	@Override
	public void addPages() {
		page = new PropertyUsageWizardPage();
		addPage(page);
	}

	@Override
	public boolean performFinish() {
		try{
			console.writeln("Starting analysis....");
			(new PropertyUsage(page.getDebug(),page.getSrc_oscar_path(),page.getProperties_path(),page.getOutput_format(),project)).findProject();			
		}catch (Exception e){
			e.printStackTrace();
			console.writeln(e.getMessage());
		}
		return true;
		
	}

}
