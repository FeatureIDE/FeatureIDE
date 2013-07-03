package br.ufal.ic.colligens.controllers.invalidproducts;

import java.awt.event.MouseEvent;
import java.util.List;

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

import br.ufal.ic.colligens.controllers.ViewController;
import br.ufal.ic.colligens.util.InvalidProductViewLog;
import br.ufal.ic.colligens.views.InvalidProductView;

public class InvalidProductsViewController extends ViewController {

	private TreeViewer treeViewer;
	private ViewContentProvider viewContentProvider;
	private ViewSorter comparator;

	private static InvalidProductsViewController INSTANCE;

	private InvalidProductsViewController() {
		super(InvalidProductView.ID);
		viewContentProvider = new ViewContentProvider();
	}

	public static InvalidProductsViewController getInstance() {
		if (INSTANCE == null) {
			INSTANCE = new InvalidProductsViewController();
		}
		return INSTANCE;
	}

	public void setInput(List<InvalidProductViewLog> list) {
		treeViewer.setInput(list);
		treeViewer.refresh();
	}

	public void clear() {
		treeViewer.setInput(null);
		treeViewer.refresh();
	}

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
					if (event.button == MouseEvent.BUTTON1 && event.count == 2) {
						Object data = clickedItem.getData();
						if (data instanceof InvalidProductViewLog) {

						}
					}
				}
			}
		});

		// Set the sorter for the table
		comparator = new ViewSorter();
		treeViewer.setComparator(comparator);

		// PlatformUI.getWorkbench().getHelpSystem()
		// .setHelp(treeViewer.getControl(), "TableView.viewer");

	}

	public void createColumns(Tree tree) {
		String[] titles = { "Variant Name", "Path" };
		int[] bounds = { 400, 400 };

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

	public void setFocus() {
		treeViewer.getControl().setFocus();
	}
}
