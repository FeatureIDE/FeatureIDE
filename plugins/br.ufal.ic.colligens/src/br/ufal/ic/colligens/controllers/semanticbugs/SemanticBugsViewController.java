package br.ufal.ic.colligens.controllers.semanticbugs;

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
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.ide.IDE;

import br.ufal.ic.colligens.controllers.ViewController;
import br.ufal.ic.colligens.models.cppchecker.CppCheckerFileLogs;
import br.ufal.ic.colligens.models.cppchecker.CppCheckerLog;
import br.ufal.ic.colligens.views.InvalidConfigurationsView;

/**
 * @author Thiago Emmanuel
 *
 */
public class SemanticBugsViewController extends ViewController {

	private TreeViewer treeViewer;
	private final ViewContentProvider viewContentProvider;

	private static SemanticBugsViewController INSTANCE;

	private SemanticBugsViewController() {
		super(InvalidConfigurationsView.ID);
		viewContentProvider = new ViewContentProvider();
	}

	public static SemanticBugsViewController getInstance() {
		if (INSTANCE == null) {
			INSTANCE = new SemanticBugsViewController();
		}
		return INSTANCE;
	}

	/**
	 * Update view
	 *
	 * @param fileProxies
	 */
	public void setInput(List<CppCheckerFileLogs> fileProxies) {
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

	public void createPartControl(Composite parent) {

		final Tree tree = new Tree(parent, SWT.H_SCROLL | SWT.V_SCROLL | SWT.FULL_SELECTION | SWT.LEFT);
		tree.setHeaderVisible(true);
		tree.setLinesVisible(true);

		treeViewer = new TreeViewer(tree);

		createColumns(tree);

		treeViewer.setContentProvider(viewContentProvider);
		treeViewer.setInput(getView().getViewSite());
		treeViewer.setLabelProvider(new ViewLabelProvider());

		final IWorkbenchPage page = getView().getSite().getPage();
		tree.addListener(SWT.MouseDown, new Listener() {

			@Override
			public void handleEvent(Event event) {
				final Point point = new Point(event.x, event.y);
				final TreeItem clickedItem = treeViewer.getTree().getItem(point);
				if (clickedItem != null) {
					final Object data = clickedItem.getData();
					if (data instanceof CppCheckerLog) {
						if ((event.button == MouseEvent.BUTTON1) && (event.count == 2)) {
							final CppCheckerLog log = (CppCheckerLog) data;
							try {

								final IEditorPart editor = IDE.openEditor(page, log.getFileLogs().getFile());
								editor.getSite().getSelectionProvider().setSelection(log);

							} catch (final PartInitException e) {
								e.printStackTrace();
							}
						}
					}
					if (data instanceof CppCheckerFileLogs) {
						if ((event.button == MouseEvent.BUTTON1) && (event.count == 2)) {

							final CppCheckerFileLogs FileLogs = (CppCheckerFileLogs) data;
							try {

								IDE.openEditor(page, FileLogs.getFile());

							} catch (final PartInitException e) {

								e.printStackTrace();
							}
						}
					}

				}
			}
		});

	}

	public void createColumns(Tree tree) {
		final String[] titles = { "Msg", "Line", "Severity", "Config", "Id" };
		final int[] bounds = { 300, 100, 100, 300, 100 };

		for (int i = 0; i < bounds.length; i++) {
			createTreeViewerColumn(tree, titles[i], bounds[i], i);
		}
	}

	private void createTreeViewerColumn(Tree tree, String title, int bound, final int ColumnNumber) {

		final int style = (ColumnNumber == 0) ? SWT.RIGHT : SWT.LEFT;

		final TreeColumn treeColumn = new TreeColumn(tree, style);

		treeColumn.setText(title);
		treeColumn.setWidth(bound);
		treeColumn.setResizable(true);
		treeColumn.setMoveable(false);
		treeColumn.addSelectionListener(getSelectionAdapter(treeColumn, ColumnNumber));
	}

	private SelectionAdapter getSelectionAdapter(final TreeColumn column, final int index) {
		final SelectionAdapter selectionAdapter = new SelectionAdapter() {

			@Override
			public void widgetSelected(SelectionEvent e) {

			}
		};
		return selectionAdapter;
	}

}
