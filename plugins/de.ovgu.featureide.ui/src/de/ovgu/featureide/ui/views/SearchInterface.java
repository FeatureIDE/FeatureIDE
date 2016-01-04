package de.ovgu.featureide.ui.views;

import org.eclipse.jface.dialogs.DialogPage;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.search.ui.ISearchPage;
import org.eclipse.search.ui.ISearchPageContainer;
import org.eclipse.search.ui.NewSearchUI;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.core.search.SearchQuery;

public class SearchInterface extends DialogPage implements ISearchPage {

	private Text txt;
	private ISearchPageContainer fContainer;
	private Button chckbox_outline;
	private Button chckbox_config;
	private Button chckbox_filesystem;  
	private final int CHECKED = 6;
	private boolean checked[];
	private Button chckbox_featureModel;
	private Button chckbox_preprocessor;
	private Button chckbox_collaborationDiagram;
	
	public SearchInterface() {
	}

	public SearchInterface(String title) {
		super(title);
	}

	public SearchInterface(String title, ImageDescriptor image) {
		super(title, image);
	}

	@Override
	public void createControl(Composite parent) {
		Composite root = new Composite(parent, SWT.NULL);
		GridLayout layout = new GridLayout(1,false);
		root.setLayout(layout);
		
		Label lbl_search = new Label(root, SWT.NONE);
		lbl_search.setLayoutData(new GridData(SWT.LEFT, SWT.CENTER, false, false,1,1));
		lbl_search.setText("Search term");
		
		// Input area
		txt = new Text(root, SWT.BEGINNING);
		txt.setLayoutData(new GridData(SWT.FILL,SWT.CENTER,true, false, 1,1 ));
		
		Label lbl_searchFor = new Label(parent, SWT.NONE);
		lbl_searchFor.setLayoutData(new GridData(SWT.LEFT,SWT.CENTER,false,false,1,1));
		lbl_searchFor.setText("Search for:");
		
		//create row layout for checkboxes
		Composite row_1 = new Composite(parent, SWT.NONE);
        row_1.setLayout(new GridLayout(3, true));
        
        row_1.setLayoutData(new GridData(SWT.FILL, SWT.BEGINNING, true, false));
        
		chckbox_outline = new Button(parent, SWT.CHECK);
		chckbox_outline.setLayoutData(new GridData(SWT.FILL, SWT.BEGINNING, true, false));
		chckbox_outline.setText("Outline");
		
		chckbox_config = new Button(parent,SWT.CHECK);
		chckbox_config.setText("Configurationseditor");
		chckbox_config.setLayoutData(new GridData(SWT.FILL, SWT.END, true, false));
		
		chckbox_featureModel = new Button(parent, SWT.CHECK);
		chckbox_featureModel.setText("Feature Model");
		
		chckbox_preprocessor = new Button(parent, SWT.CHECK);
		chckbox_preprocessor.setText("Files (?)");
		
		chckbox_filesystem = new Button(parent, SWT.CHECK);
		chckbox_filesystem.setText("File System");
		
		chckbox_collaborationDiagram = new Button(parent, SWT.CHECK);
		chckbox_collaborationDiagram.setText("Collaboration Diagram");
		
		setControl(root);

	}
	
	private boolean evaluateCheckBoxes(){
		/**array definitions (=where to search)
		 * 0...Outline
		 * 1...Configuration Editor
		 * 2...File System
		 * 3...Feature Model
		 * 4...Files
		 * 5...Collaboration Diagram
		 */
		//count the amount of selections
		int selections = 0;
		checked = new boolean[CHECKED];
		if (chckbox_outline.getSelection()){
			checked[0] = true;
			selections++;
		}
		if (chckbox_config.getSelection()){
			checked[1] = true;
			selections++;
		}
		if (chckbox_filesystem.getSelection()){
			checked[2] = true;
			selections++;
		}
		if (chckbox_featureModel.getSelection()){
			checked[3] = true;
			selections++;
		}
		if (chckbox_preprocessor.getSelection()){
			checked[4] = true;
			selections++;
		}
		if (chckbox_collaborationDiagram.getSelection()){
			checked[5] = true;
			selections++;
		}
		if (selections == 0)
			return false;
		return true;
	}

	@Override
	public boolean performAction() {
		if (evaluateCheckBoxes() && txt.getText().length() != 0){
			SearchQuery query = new SearchQuery(txt.getText(),checked,CHECKED);
			NewSearchUI.runQueryInForeground(fContainer.getRunnableContext(), query);
			return true;
		}
		return false;
	}

	@Override
	public void setContainer(ISearchPageContainer container) {
		fContainer = container;
		
	}

}
