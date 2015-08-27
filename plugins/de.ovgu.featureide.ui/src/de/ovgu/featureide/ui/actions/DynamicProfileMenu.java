package de.ovgu.featureide.ui.actions;

import static de.ovgu.featureide.fm.core.localization.StringTable.NO_COLORSCHEME_SELECTED;

import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.internal.ui.packageview.PackageFragmentRootContainer;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.ContributionItem;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeSelection;
import org.eclipse.jface.viewers.TreePath;
import org.eclipse.jface.viewers.TreeSelection;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.ui.ISelectionService;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.internal.Workbench;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.ColorschemeTable;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.ProfileManager;
import de.ovgu.featureide.fm.ui.PlugInProfileSerializer;

/**
 * Class to add the profilemenu to the contextmenu of the project (projectonly)
 * 
 * @author Jonas Weigt
 * @author Christian Harnisch
 */

@SuppressWarnings({ "unused", "restriction" })
public class DynamicProfileMenu extends ContributionItem {
	private AddProfileColorSchemeAction addProfileSchemeAction;
	private RenameProfileColorSchemeAction renameProfileSchemeAction;
	private DeleteProfileColorSchemeAction deleteProfileSchemeAction;
	private IFeatureProject myFeatureProject = getCurrentFeatureProject();
	private FeatureModel myFeatureModel = myFeatureProject.getFeatureModel();
	private boolean multipleSelected = isMultipleSelection();

	/*
	 * Constructors
	 */
	public DynamicProfileMenu() {

	}

	public DynamicProfileMenu(String id) {
		super(id);
	}
	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.action.ContributionItem#fill(org.eclipse.swt.widgets.Menu, int)
	 * 
	 * creates dynamic menu 
	 */
	@Override
	public void fill(Menu menu, int index) {

		/*
		 * 		final IFeatureProject res = (IFeatureProject) SelectionWrapper.init((IStructuredSelection)PlatformUI.getWorkbench().getActiveWorkbenchWindow().getSelectionService().getSelection(), IProject.class);
		 *		myFeatureModel = res.getFeatureModel();
		 *		myFeatureProject = res;
		 *	
		 *		maybe another solution for getting the current project or structured selection 
		 *
		 */

		MenuManager man = new MenuManager("Profile", PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(ISharedImages.IMG_OBJ_ADD), "");
		man.addMenuListener(new IMenuListener() {
			public void menuAboutToShow(IMenuManager m) {

				fillContextMenu(m);
			}
		});

		if (multipleSelected == false) {
			man.fill(menu, index);
		}

		man.setVisible(true);
		createActions();

	}

	/*
	 * this method fills the menumanager with actionbuttons
	 */
	private void fillContextMenu(IMenuManager menuMgr) {
		FeatureModel fm = myFeatureModel;
		ColorschemeTable colorschemeTable = fm.getColorschemeTable();
		List<String> csNames = colorschemeTable.getColorschemeNames();
		
		ProfileManager.Project project = ProfileManager.getProject(fm.xxxGetEclipseProjectPath(), PlugInProfileSerializer.FEATURE_PROJECT_SERIALIZER);
		final String curColorSchemeName = ProfileManager.getProject(fm.xxxGetEclipseProjectPath(), PlugInProfileSerializer.FEATURE_PROJECT_SERIALIZER).getActiveProfile().getName();
		
		
		
		for (String name : project.getProfileNames()) {
			SetProfileColorSchemeAction setCSAction = new SetProfileColorSchemeAction(name, Action.AS_CHECK_BOX, myFeatureModel);
			if (name.equals(curColorSchemeName)) {
				setCSAction.setChecked(true);
			}
			menuMgr.add(setCSAction);

		}
		menuMgr.add(new Separator());
		menuMgr.add(addProfileSchemeAction);
		menuMgr.add(renameProfileSchemeAction);
		menuMgr.add(deleteProfileSchemeAction);
		colorschemeTable.readColorsFromFile(getCurrentFeatureProject().getProject());

		/*
		 * disables rename and delete when default colorscheme is selected
		 */
		if (curColorSchemeName.equals("Default")) {
			renameProfileSchemeAction.setEnabled(false);
			deleteProfileSchemeAction.setEnabled(false);
		}

		menuMgr.setRemoveAllWhenShown(true);
	}

	/*
	 * this methods creates functionality of the actionbuttons
	 */

	private void createActions() {
		addProfileSchemeAction = new AddProfileColorSchemeAction("Add Colorscheme", myFeatureModel, myFeatureProject);
		renameProfileSchemeAction = new RenameProfileColorSchemeAction("Change Name", myFeatureModel, myFeatureProject);
		deleteProfileSchemeAction = new DeleteProfileColorSchemeAction("Delete Colorscheme", myFeatureModel);

	}
	/*
	 * Returns selection of type IStructuredSelection
	 */
	private static IStructuredSelection getIStructuredCurrentSelection() {
		ISelectionService selectionService = Workbench.getInstance().getActiveWorkbenchWindow().getSelectionService();

		ISelection selection = selectionService.getSelection();
		return (IStructuredSelection) selection;

	}

	/*
	 *  this method disables the profilemenu, if more than one project is selected
	 */
	private static boolean isMultipleSelection() {
		
		IStructuredSelection myselection = getIStructuredCurrentSelection();

		if (myselection instanceof ITreeSelection) {
			TreeSelection treeSelection = (TreeSelection) myselection;
			TreePath[] treePaths = treeSelection.getPaths();
			if (treePaths.length > 1) {
				return true;
				
			}
		}
		return false;

	}

	/*
	 * Returns selected FeatureProject
	 */
	private static IFeatureProject getCurrentFeatureProject() {
		Object element = getIStructuredCurrentSelection().getFirstElement();

		IProject project = null;

		if (element instanceof IResource) {
			project = ((IResource) element).getProject();
		} else if (element instanceof PackageFragmentRootContainer) {
			IJavaProject jProject = ((PackageFragmentRootContainer) element).getJavaProject();
			project = jProject.getProject();
		} else if (element instanceof IJavaElement) {
			IJavaProject jProject = ((IJavaElement) element).getJavaProject();
			project = jProject.getProject();

		}
		IFeatureProject myproject = CorePlugin.getFeatureProject(project);
		return myproject;
	}

}
