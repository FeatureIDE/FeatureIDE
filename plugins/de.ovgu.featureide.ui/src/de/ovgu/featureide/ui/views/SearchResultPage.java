package de.ovgu.featureide.ui.views;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.eclipse.core.filesystem.EFS;
import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.viewers.AbstractTreeViewer;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
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
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IMemento;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.part.IPageSite;

import de.ovgu.featureide.core.search.ResultEvent;

public class SearchResultPage implements ISearchResultPage, ISearchResultListener {

	private String id;
	private Composite root;
	private IPageSite site;
	private TreeViewer viewer;
	private Tree tree;
	private DoubleClickListener listener;
	
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
		
		listener = new DoubleClickListener();
		
		tree = new Tree();
	
		viewer = new TreeViewer(root, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);
		viewer.setContentProvider(new TreeContentProvider());
		viewer.setLabelProvider(new TreeLabelProvider());
		viewer.setInput(tree);
		viewer.addDoubleClickListener(listener);
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
			tree = new Tree();
			viewer.setInput(tree);
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
						File f = ((ResultEvent) e).getResult().getFile();
						List<File> list;
						try {
							list = SearchResultPage.generateFilePath(f);
							tree.addBranch(list, 0);
							viewer.refresh();
						} catch (IOException e1) {
							e1.printStackTrace();
						}
					}
					if (((ResultEvent) e).getResult().isFeature()){
						//todo
					}
				}
			});
		}
	}
	
	public static List<File> generateFilePath(File f) throws IOException{
		List<File> list = new ArrayList<File>();
		File file =f;
		File workspace = ResourcesPlugin.getWorkspace().getRoot().getLocation().toFile();
		while (! file.getAbsolutePath().equals(workspace.getAbsolutePath())){
			list.add(file);
			file = file.getParentFile();
		}
		Collections.reverse(list);
		return list;
	}
	
	class Tree{
		
		private boolean isRoot;
		private boolean isChild;
		private File f;
		private Tree parent;
		private List <Tree> childs;
		private Tree child;
		
		public Tree(){
			isRoot = true;
			isChild = false;
			f = ResourcesPlugin.getWorkspace().getRoot().getLocation().toFile();
			parent = null;
			childs = new ArrayList<Tree>();
			child = null;
		}
		
		private Tree(File f,Tree parent){
			isRoot = false;
			isChild = true;
			this.parent = parent;
			childs = null;
			child = null;
			this.f = f;
		}
		
		public boolean hasChilds(){
			if (isRoot){
				return !childs.isEmpty();
			}
			if(isChild){
				return child != null;
			}
			return false;
		} 
		
		private Tree createBranch(List<File> l, int index){
			Tree t = new Tree(l.get(index),this);
			if(index < l.size()-1)
				t.child = createBranch(l, index+1);
			return t;
		}
		
		public List<Tree> getChilds(){
			if (isRoot)
				return childs;
			if (isChild){
				List<Tree> l = new ArrayList<Tree>();
				l.add(child);
				return l;
			}
			return null;
		}
		
		public void addBranch(List<File> l, int index){
			Tree temp = createBranch(l,index);
			childs.add(temp);
		}
		
		public File getFile(){
			return f;
		}
		
		public Tree getParent(){
			return parent;
		}
		
		public boolean isRoot(){
			return isRoot;
		}
		
	}
	
	class TreeContentProvider implements ITreeContentProvider {

		@Override
		public void dispose() {
		}

		@Override
		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		}

		@Override
		public Object[] getElements(Object inputElement) {
			return ((Tree) inputElement).getChilds().toArray();
		}

		@Override
		public Object[] getChildren(Object parentElement) {
			return ((Tree) parentElement).getChilds().toArray();
		}


		@Override
		public Object getParent(Object element) {
			return ((Tree) element).getParent();
		}


		@Override
		public boolean hasChildren(Object element) {
			return ((Tree)element).hasChilds();
		}
		
	}
	
	public class TreeLabelProvider extends LabelProvider{
		@Override
		public String getText(Object element) {
			if (((Tree) element).isRoot())
				return "";
			File f = ((Tree) element).getFile();
			return f.getName();
		}
	}
	
	public class DoubleClickListener implements IDoubleClickListener
	{
	  @Override
	  public void doubleClick(final DoubleClickEvent event)
	  {
	    final IStructuredSelection selection = (IStructuredSelection)event.getSelection();
	    if (selection == null || selection.isEmpty())
	      return;

	    final Object sel = selection.getFirstElement();

	    final ITreeContentProvider provider = (ITreeContentProvider)viewer.getContentProvider();

	    if (!provider.hasChildren(sel)){
	    	File file = ((Tree)sel).getFile();
	    	IFileStore fileStore = EFS.getLocalFileSystem().getStore(file.toURI());
	        IWorkbenchPage page = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
	        try {
				IDE.openEditorOnFileStore( page, fileStore );
			} catch (PartInitException e) {
				e.printStackTrace();
			}
	    }
	    
	    if (viewer.getExpandedState(sel))
	        viewer.collapseToLevel(sel, AbstractTreeViewer.ALL_LEVELS);
	      else
	        viewer.expandToLevel(sel, 1);
	  }
	}
	
}
