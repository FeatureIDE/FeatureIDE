package featureide.ui.perspective;

import org.eclipse.ui.IFolderLayout;
import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.internal.cheatsheets.CheatSheetPlugin;
import org.eclipse.ui.internal.cheatsheets.ICheatSheetResource;
import org.eclipse.ui.internal.cheatsheets.views.CheatSheetView;

import de.ovgu.featureide.ui.ahead.AheadUIPlugin;
import de.ovgu.featureide.ui.ahead.wizards.NewJakFileWizard;

import featureide.ui.UIPlugin;
import featureide.ui.wizards.NewEquationFileWizard;
import featureide.ui.wizards.NewFeatureProjectWizard;
/**
 * 
 * Create the FeatureIDE perspective
 * 
 * @author Christian Becker
 * @author Thomas Thuem
 */
@SuppressWarnings("restriction")
public class PerspectiveFactory implements IPerspectiveFactory {
	
	public static final String ID = UIPlugin.PLUGIN_ID + ".FeatureIDEperspective";
	
	private String ConsoleView="org.eclipse.ui.console.ConsoleView";
	private String JavaPackageExplorer="org.eclipse.jdt.ui.PackageExplorer";
	private String FeatureModelEditView="featureide.fm.ui.views.FeatureModelEditView";
	private String LaunchActions="org.eclipse.debug.ui.launchActionSet";
	
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
		
		down.addView(ConsoleView);
		down.addView(FeatureModelEditView);
		down.addView(IPageLayout.ID_PROBLEM_VIEW);
		
		left.addView(JavaPackageExplorer);	
			
		layout.addShowViewShortcut("org.eclipse.ui.cheatsheets.views.CheatSheetView");
	    layout.addShowViewShortcut(FeatureModelEditView);
	    layout.addShowViewShortcut(IPageLayout.ID_RES_NAV);
	    layout.addShowViewShortcut(IPageLayout.ID_OUTLINE);
	    layout.addShowViewShortcut(IPageLayout.ID_TASK_LIST);            
	   	
		addActions();
		display_cheatsheet();
	}
	private void addActions(){
		layout.addActionSet(AheadUIPlugin.PLUGIN_ID+".NewFiles");
		layout.addActionSet(UIPlugin.PLUGIN_ID + ".NewFiles");
		layout.addActionSet(LaunchActions);

	}
	
	private void display_cheatsheet(){
        CheatSheetView view;
        IWorkbench workbench = CheatSheetPlugin.getPlugin().getWorkbench();
        IWorkbenchWindow window = workbench.getActiveWorkbenchWindow();
        IWorkbenchPage page = window.getActivePage();

        view = (CheatSheetView) page.findView(ICheatSheetResource.CHEAT_SHEET_VIEW_ID);
        if (view == null) {
                try {
                        view = (CheatSheetView)page.showView(ICheatSheetResource.CHEAT_SHEET_VIEW_ID);
                        view.setInput("de.ovgu.featureide.ui.doc.cheatsheet");
                       
                } catch (PartInitException e) {
                       
                        e.printStackTrace();
                }
                page.activate(view);
        }
	}
	
}
