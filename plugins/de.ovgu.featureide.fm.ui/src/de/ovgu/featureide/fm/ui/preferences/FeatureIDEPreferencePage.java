package de.ovgu.featureide.fm.ui.preferences;

import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

import de.ovgu.featureide.fm.core.configuration.Configuration;

public class FeatureIDEPreferencePage extends PreferencePage implements
		IWorkbenchPreferencePage {
	
	private SelectionListener selectionListener = new SelectionListener() {
		@Override
		public void widgetSelected(SelectionEvent e) {
			Configuration.setDefaultCompletion((Integer) ((Button) e.getSource()).getData());
		}
		
		@Override
		public void widgetDefaultSelected(SelectionEvent e) {
		}
	};

	public FeatureIDEPreferencePage() {
	}

	public FeatureIDEPreferencePage(String title) {
		super(title);
	}

	public FeatureIDEPreferencePage(String title, ImageDescriptor image) {
		super(title, image);
	}

	@Override
	public void init(IWorkbench workbench) {
	}

	@Override
	protected Control createContents(Composite parent) {
		Composite container = new Composite(parent, SWT.NULL);		
		final FillLayout fillLayout = new FillLayout();
		container.setLayout(fillLayout);
		
		Group group1 = new Group(container, SWT.SHADOW_IN);
	    group1.setText("Configuration Coloring");
	    group1.setLayout(new RowLayout(SWT.VERTICAL));
	    Button noneButton = new Button(group1, SWT.RADIO);
	    Button openClauseButton = new Button(group1, SWT.RADIO);
	    Button contradictionButton = new Button(group1, SWT.RADIO);

	    noneButton.setData(Configuration.COMPLETION_NONE);
	    openClauseButton.setData(Configuration.COMPLETION_OPEN_CLAUSES);
	    contradictionButton.setData(Configuration.COMPLETION_ONE_CLICK);
	    
	    noneButton.addSelectionListener(selectionListener);
	    openClauseButton.addSelectionListener(selectionListener);
	    contradictionButton.addSelectionListener(selectionListener);
	    
	    noneButton.setText("None");
	    openClauseButton.setText("Check open clauses (Faster results)");
	    contradictionButton.setText("Check contradiction (Better results)");
	    
	    switch (Configuration.getDefaultCompletion()) {
	    	case Configuration.COMPLETION_NONE:
		    	noneButton.setSelection(true);
		    	break;
	    	case Configuration.COMPLETION_OPEN_CLAUSES:
	    		openClauseButton.setSelection(true);
		    	break;
	    	case Configuration.COMPLETION_ONE_CLICK:
	    		contradictionButton.setSelection(true);
		    	break;
	    }
	    
		return container;
	}
}
