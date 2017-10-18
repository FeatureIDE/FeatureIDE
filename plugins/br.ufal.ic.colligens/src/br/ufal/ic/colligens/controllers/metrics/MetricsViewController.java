package br.ufal.ic.colligens.controllers.metrics;

import static de.ovgu.featureide.fm.core.localization.StringTable.METRICS;
import static de.ovgu.featureide.fm.core.localization.StringTable.VALUE;

import java.util.List;

import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TableViewerColumn;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.ui.PlatformUI;

import br.ufal.ic.colligens.controllers.ViewController;
import br.ufal.ic.colligens.util.metrics.Metrics;
import br.ufal.ic.colligens.views.MetricsView;

public class MetricsViewController extends ViewController {

	private TableViewer tableViewer;
	private MetricsView view;
	private final ViewContentProvider viewContentProvider;

	private static MetricsViewController INSTANCE;

	private MetricsViewController() {
		super(MetricsView.ID);
		viewContentProvider = new ViewContentProvider();
	}

	public static MetricsViewController getInstance() {
		if (INSTANCE == null) {
			INSTANCE = new MetricsViewController();
		}
		return INSTANCE;
	}

	public TableViewer getViewer() {
		return tableViewer;
	}

	public void setViewer(TableViewer tableViewer) {
		this.tableViewer = tableViewer;
	}

	@Override
	public MetricsView getView() {
		return view;
	}

	public void setView(MetricsView view) {
		this.view = view;
	}

	public void setInput(List<Metrics> list) {
		tableViewer.setInput(list);
		tableViewer.refresh();
	}

	public void clear() {
		tableViewer.setInput(null);
		tableViewer.refresh();
	}

	public void createPartControl(Composite parent) {
		tableViewer = new TableViewer(parent, SWT.H_SCROLL | SWT.V_SCROLL | SWT.FULL_SELECTION | SWT.LEFT);
		createColumns(parent);
		final Table table = tableViewer.getTable();

		tableViewer.setContentProvider(viewContentProvider);
		tableViewer.setInput(view.getViewSite());
		tableViewer.setLabelProvider(new ViewLabelProvider());
		table.setHeaderVisible(true);
		table.setLinesVisible(true);

		PlatformUI.getWorkbench().getHelpSystem().setHelp(tableViewer.getControl(), "TableView.viewer");

	}

	public void createColumns(Composite parent) {
		final String[] titles = { METRICS, VALUE };
		final int[] bounds = { 300, 400 };

		for (int i = 0; i < bounds.length; i++) {
			createTableViewerColumn(titles[i], bounds[i], i);
		}
	}

	public TableViewerColumn createTableViewerColumn(String title, int bound, final int colNumber) {
		final TableViewerColumn viewerColumn = new TableViewerColumn(tableViewer, SWT.LEFT);
		final TableColumn column = viewerColumn.getColumn();
		column.setText(title);
		column.setWidth(bound);
		column.setResizable(true);
		column.setMoveable(false);
		return viewerColumn;
	}

	public void setFocus() {
		tableViewer.getControl().setFocus();
	}
}
