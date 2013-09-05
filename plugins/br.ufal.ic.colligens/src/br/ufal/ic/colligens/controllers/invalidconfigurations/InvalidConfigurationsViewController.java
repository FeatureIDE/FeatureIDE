package br.ufal.ic.colligens.controllers.invalidconfigurations;

import java.awt.event.MouseEvent;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeColumn;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.ide.IDE;

import br.ufal.ic.colligens.controllers.ViewController;
import br.ufal.ic.colligens.models.FileProxy;
import br.ufal.ic.colligens.util.Log;
import br.ufal.ic.colligens.views.InvalidConfigurationsView;

/**
 * @author Thiago Emmanuel
 * 
 */
public class InvalidConfigurationsViewController extends ViewController {

	private TreeViewer treeViewer;
	private ViewContentProvider viewContentProvider;
	private ViewSorter comparator;
	private static InvalidConfigurationsViewController INSTANCE;

	private InvalidConfigurationsViewController() {
		super(InvalidConfigurationsView.ID);
		this.viewContentProvider = new ViewContentProvider();
	}

	public static InvalidConfigurationsViewController getInstance() {
		if (INSTANCE == null) {
			INSTANCE = new InvalidConfigurationsViewController();
		}
		return INSTANCE;
	}
	/**
	 * Update view
	 * 
	 * @param fileProxies
	 */
	public void setInput(List<FileProxy> fileProxies) {
		treeViewer.setInput(fileProxies);
		treeViewer.refresh();
	}

	public void clear() {
		if (treeViewer == null) {
			return;
		}
		treeViewer.setInput(null);
		treeViewer.refresh();
	}

	public boolean isEmpty() {
		if (treeViewer == null) {
			return true;
		}
		if (treeViewer.getInput() == null) {
			return true;
		} else {
			if (treeViewer.getInput() instanceof List) {
				return ((List<?>) treeViewer.getInput()).isEmpty();
			}
		}
		return true;
	}

	public void setFocus() {
		treeViewer.getControl().setFocus();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.part.WorkbenchPartn#createPartControl(Composite)
	 */
	public void createPartControl(Composite parent) {

		Tree tree = new Tree(parent, SWT.H_SCROLL | SWT.V_SCROLL
				| SWT.FULL_SELECTION | SWT.LEFT);
		tree.setHeaderVisible(true);
		tree.setLinesVisible(true);

		treeViewer = new TreeViewer(tree);

		this.createColumns(tree);

		treeViewer.setContentProvider(this.viewContentProvider);
		treeViewer.setInput(getView().getViewSite());
		treeViewer.setLabelProvider(new ViewLabelProvider());

		tree.addListener(SWT.MouseDown, new Listener() {

			@Override
			public void handleEvent(Event event) {
				Point point = new Point(event.x, event.y);
				TreeItem clickedItem = treeViewer.getTree().getItem(point);
				if (clickedItem != null) {
					Object data = clickedItem.getData();
					if (data instanceof Log) {
						if (event.button == MouseEvent.BUTTON1
								&& event.count == 2) {
							final Log log = (Log) data;
							try {

								IEditorPart editor = IDE.openEditor(getView()
										.getSite().getPage(), log.getFile());
								editor.getSite().getSelectionProvider()
										.setSelection(log.selection());

							} catch (PartInitException e) {
								// TODO Auto-generated catch block
								e.printStackTrace();
							}
						}
					}
					if (data instanceof FileProxy) {
						if (event.button == MouseEvent.BUTTON1
								&& event.count == 2) {

							final FileProxy fileProxy = (FileProxy) data;
							try {

								IDE.openEditor(getView().getSite().getPage(),
										(IFile) fileProxy.getFileIResource());

							} catch (PartInitException e) {
								// TODO Auto-generated catch block
								e.printStackTrace();
							}
						}
					}

				}
			}
		});

		// // Set the sorter for the table
		comparator = new ViewSorter();
		treeViewer.setComparator(comparator);

		// PlatformUI.getWorkbench().getHelpSystem()
		// .setHelp(tableViewer.getControl(), "TableView.viewer");
	}

	public void createColumns(Tree tree) {
		String[] titles = { "Description", "Resource", "Path",
				"Feature configuration", "Severity" };
		int[] bounds = { 300, 100, 100, 300, 100 };

		for (int i = 0; i < bounds.length; i++) {
			this.createTreeViewerColumn(tree, titles[i], bounds[i], i);
		}
	}

	private void createTreeViewerColumn(Tree tree, String title, int bound,
			final int ColumnNumber) {

		int style = (ColumnNumber == 0) ? SWT.RIGHT : SWT.LEFT;

		final TreeColumn treeColumn = new TreeColumn(tree, style);

		treeColumn.setText(title);
		treeColumn.setWidth(bound);
		treeColumn.setResizable(true);
		treeColumn.setMoveable(false);
		treeColumn.addSelectionListener(this.getSelectionAdapter(treeColumn,
				ColumnNumber));
	}

	private SelectionAdapter getSelectionAdapter(final TreeColumn column,
			final int index) {
		SelectionAdapter selectionAdapter = new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				comparator.setColumn(index);
				int direction = comparator.getDirection();
				treeViewer.getTree().setSortDirection(direction);
				treeViewer.getTree().setSortColumn(column);
				treeViewer.refresh();
			}
		};
		return selectionAdapter;
	}

}
