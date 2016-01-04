package de.ovgu.featureide.ui.views;

import org.eclipse.search.ui.ISearchResult;
import org.eclipse.search.ui.ISearchResultListener;
import org.eclipse.search.ui.ISearchResultPage;
import org.eclipse.search.ui.ISearchResultViewPart;
import org.eclipse.search.ui.SearchResultEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IMemento;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.IPageSite;

import de.ovgu.featureide.core.search.ResultEvent;

public class SearchResultPage implements ISearchResultPage, ISearchResultListener {

	private String id;
	private Composite root;
	private IPageSite site;
	private Text txt;
	
	@Override
	public IPageSite getSite() {
		return site;
	}

	@Override
	public void init(IPageSite site) throws PartInitException {
		this.site = site;
	}

	@Override
	public void createControl(Composite parent) {
		root = new Composite(parent, SWT.NULL);
		root.setLayout(new FillLayout(SWT.HORIZONTAL));

		txt = new Text(root, SWT.BORDER | SWT.READ_ONLY | SWT.H_SCROLL | SWT.V_SCROLL | SWT.CANCEL | SWT.MULTI);
	}

	@Override
	public void dispose() {
	}

	@Override
	public Control getControl() {
		return root;
	}

	@Override
	public void setActionBars(IActionBars actionBars) {
	}

	@Override
	public void setFocus() {
		root.setFocus();
	}

	@Override
	public Object getUIState() {
		return null;
	}

	@Override
	public void setInput(ISearchResult search, Object uiState) {
		if(search == null){
			txt.setText("");
			return;
		}
		search.addListener(this);
	}

	@Override
	public void setViewPart(ISearchResultViewPart part) {
	}

	@Override
	public void restoreState(IMemento memento) {

	}

	@Override
	public void saveState(IMemento memento) {
	}

	@Override
	public void setID(String id) {
		this.id = id;
	}

	@Override
	public String getID() {
		return id;
	}

	@Override
	public String getLabel() {
		return "Search results";
	}

	@Override
	public void searchResultChanged(final SearchResultEvent e) {
		if (e instanceof ResultEvent) {
			Display.getDefault().asyncExec(new Runnable() {
				@Override
				public void run() {
					if (((ResultEvent) e).getResult().isFile()){
						String newText = txt.getText() + "\n" + ((ResultEvent) e).getResult().getFile().getAbsolutePath();
						txt.setText(newText);
					}
					if (((ResultEvent) e).getResult().isFeature()){
						String newText = txt.getText() + "\n" + ((ResultEvent) e).getResult().getFeature();
						txt.setText(newText);
					}
				}
			});
		}
	}

	
	
}
