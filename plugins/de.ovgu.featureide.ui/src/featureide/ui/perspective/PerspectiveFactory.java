package featureide.ui.perspective;

import org.eclipse.ui.IFolderLayout;
import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;

import de.ovgu.featureide.ui.ahead.actions.StartJakFileWizard;
import de.ovgu.featureide.ui.ahead.wizards.NewJakFileWizard;

import featureide.fm.ui.views.FeatureModelEditView;
import featureide.ui.UIPlugin;
import featureide.ui.wizards.NewEquationFileWizard;
import featureide.ui.wizards.NewFeatureProjectWizard;
/**
 * 
 * TODO description
 * 
 * @author Christian Becker
 * @author Thomas Thuem
 */
public class PerspectiveFactory implements IPerspectiveFactory {
	
	public static final String ID = UIPlugin.PLUGIN_ID + ".FeatureIDEperspective";
	
	private IPageLayout layout;

	@Override
	public void createInitialLayout(IPageLayout layout) {
		this.layout=layout;
        String editorArea = layout.getEditorArea();
        
		//TODO Chris: find a way to dynamically add wizard, let them layout somewhere
		layout.addNewWizardShortcut(NewEquationFileWizard.ID);
		//layout.addNewWizardShortcut(NewJakFileWizard.ID);
		layout.addNewWizardShortcut(NewFeatureProjectWizard.ID);
		layout.addNewWizardShortcut(NewJakFileWizard.ID);
		
        IFolderLayout left = layout.createFolder("left", IPageLayout.LEFT, (float) 0.23, editorArea);
		IFolderLayout down=layout.createFolder("down", IPageLayout.BOTTOM, (float)0.80, editorArea); 
		
		down.addView("org.eclipse.ui.console.ConsoleView");
		down.addView("featureide.fm.ui.views.FeatureModelEditView");
		down.addView(IPageLayout.ID_PROBLEM_VIEW);
		
		left.addView("org.eclipse.jdt.ui.PackageExplorer");
	//	left.addView(IPageLayout.ID_RES_NAV);
		
	   
	    layout.addShowViewShortcut(FeatureModelEditView.ID);
	    layout.addShowViewShortcut(IPageLayout.ID_RES_NAV);
	    layout.addShowViewShortcut(IPageLayout.ID_OUTLINE);
	    layout.addShowViewShortcut(IPageLayout.ID_TASK_LIST);            
	   	
		addActions();
	}
	private void addActions(){
		layout.addActionSet(StartJakFileWizard.ID);
		layout.addActionSet(UIPlugin.PLUGIN_ID + ".NewFiles");
		layout.addActionSet("org.eclipse.debug.ui.launchActionSet");
		
	}
}
