package de.ovgu.featureide.cloneanalysis.views;

import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeTableColumn;
import javafx.scene.control.TreeTableView;
import javafx.scene.control.cell.PropertyValueFactory;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;

import de.ovgu.featureide.cloneanalysis.results.CloneAnalysisResults;
import de.ovgu.featureide.cloneanalysis.results.VariantAwareClone;

/**
 * This sample class demonstrates how to plug-in a new workbench view. The view
 * shows data obtained from the model. The sample creates a dummy model on the
 * fly, but a real implementation would connect to the model available either in
 * this or another plug-in (e.g. the workspace). The view is connected to the
 * model using a content provider.
 * <p>
 * The view uses a label provider to define how model objects should be
 * presented in the view. Each view can present the same model objects using
 * different labels and icons, if needed. Alternatively, a single label provider
 * can be shared between views in order to ensure that objects of the same type
 * are presented in the same way everywhere.
 * <p>
 */

public class FancyCloneAnalysisView extends ViewPart {

	/**
	 * The ID of the view as specified by the extension.
	 */
	public static final String ID = "de.ovgu.featureide.code.cloneanalysis.views.CloneAnalysisView";

	private TreeTableView<VariantAwareClone> matchViewer;

	private Action action1;
	private Action action2;
	// private Action doubleClickAction;

	/*
	 * The content provider class is responsible for providing objects to the
	 * view. It can wrap existing objects in adapters or simply return objects
	 * as-is. These objects may be sensitive to the current input of the view,
	 * or ignore it and always show the same content (like Task List, for
	 * example).
	 */

	// class CloneAnalysisContentProvider implements IStructuredContentProvider
	// {
	// public void inputChanged(Viewer v, Object oldInput, Object newInput)
	// {}
	//
	// public void dispose()
	// {}
	//
	// public Object[] getElements(Object parent)
	// {
	// return clones.toArray();
	// }
	// }
	//
	// class NameSorter extends ViewerSorter
	// {}

	/**
	 * The constructor.
	 */
	public FancyCloneAnalysisView() {

	}

	public void updateAnalysis(IStructuredSelection selection) {

	}

	/**
	 * This is a callback that will allow us to create the viewer and initialize
	 * it.
	 */
	public void createPartControl(Composite parent) {
		// matchViewer = new TableViewer(parent, SWT.MULTI | SWT.H_SCROLL |
		// SWT.V_SCROLL);
		// matchViewer.setContentProvider(new CloneAnalysisContentProvider());
		// matchViewer.setLabelProvider(new CloneAnalysisLabelProvider());
		// matchViewer.setSorter(new NameSorter());
		// matchViewer.setInput(getViewSite());
		//
		// // Create the help context id for the viewer's control
		// PlatformUI.getWorkbench().getHelpSystem()
		// .setHelp(matchViewer.getControl(),
		// "de.ovgu.featureide.code.Cloneanalysis.viewer");
		matchViewer = new TreeTableView<VariantAwareClone>();
		// matchViewer.set
		createColumns();

		makeActions();
		hookContextMenu();
		hookDoubleClickAction();
		contributeToActionBars();
	}

	private void createColumns() {
		TreeTableColumn<VariantAwareClone, String> column = new TreeTableColumn<VariantAwareClone, String>(
				"first Column");
		column.setCellValueFactory(new PropertyValueFactory("code"));
		matchViewer.getColumns().set(0, column);
	}

	private void hookContextMenu() {// TODO
		MenuManager menuMgr = new MenuManager("#PopupMenu");
		menuMgr.setRemoveAllWhenShown(true);
		menuMgr.addMenuListener(new IMenuListener() {
			public void menuAboutToShow(IMenuManager manager) {
				FancyCloneAnalysisView.this.fillContextMenu(manager);
			}
		});
		// Menu menu = menuMgr.createContextMenu(matchViewer.getControl());
		// matchViewer.getControl().setMenu(menu);
		// getSite().registerContextMenu(menuMgr, matchViewer);
	}

	private void contributeToActionBars() {
		IActionBars bars = getViewSite().getActionBars();
		fillLocalPullDown(bars.getMenuManager());
		fillLocalToolBar(bars.getToolBarManager());
	}

	private void fillLocalPullDown(IMenuManager manager) {
		manager.add(action1);
		manager.add(new Separator());
		manager.add(action2);
	}

	private void fillContextMenu(IMenuManager manager) {
		manager.add(action1);
		manager.add(action2);
		// Other plug-ins can contribute there actions here
		manager.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
	}

	private void fillLocalToolBar(IToolBarManager manager) {
		manager.add(action1);
		manager.add(action2);
	}

	private void makeActions() {
		action1 = new Action() {
			public void run() {
				showMessage("Action 1 executed");
			}
		};
		action1.setText("Action 1");
		action1.setToolTipText("Action 1 tooltip");
		action1.setImageDescriptor(
				PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(ISharedImages.IMG_OBJS_INFO_TSK));

		action2 = new Action() {
			public void run() {
				showMessage("Action 2 executed");
			}
		};
		action2.setText("Action 2");
		action2.setToolTipText("Action 2 tooltip");
		action2.setImageDescriptor(
				PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(ISharedImages.IMG_OBJS_INFO_TSK));
		// doubleClickAction = new Action()
		// {
		// public void run()
		// {
		// TreeItem<VariantAwareClone> selectedItem =
		// matchViewer.getSelectionModel().getSelectedItem();
		// showMessage("Double-click detected on " + selectedItem.toString());
		// }
		// };
	}

	private void hookDoubleClickAction() {
		// matchViewer.addDoubleClickListener(new IDoubleClickListener()
		// {
		// public void doubleClick(DoubleClickEvent event)
		// {
		// doubleClickAction.run();
		// }
		// });
	}

	private void showMessage(String message) {
		// MessageDialog.openInformation(matchViewer.getControl().getShell(),
		// "Sample View", message);
	}

	/**
	 * Passing the focus request to the viewer's control.
	 */
	public void setFocus() {
		// matchViewer.getControl().setFocus();
	}

	public void showResults(CloneAnalysisResults<VariantAwareClone> formattedResults) {
		TreeItem<VariantAwareClone> root = new TreeItem<VariantAwareClone>();
		for (VariantAwareClone clone : formattedResults.getClones()) {
			TreeItem<VariantAwareClone> item = new TreeItem<VariantAwareClone>(clone);
			root.getChildren().add(item);
		}
		matchViewer.setRoot(root);

		// matchViewer.refresh();
	}
}