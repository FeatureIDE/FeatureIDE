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

import de.ovgu.featureide.fm.core.Preferences;

public class FeatureIDEPreferencePage extends PreferencePage implements
		IWorkbenchPreferencePage {
	
	private static final SelectionListener completionSelectionListener = new SelectionListener() {
		@Override
		public void widgetSelected(SelectionEvent e) {
			Preferences.setDefaultCompletion((Integer) ((Button) e.getSource()).getData());
		}
		
		@Override
		public void widgetDefaultSelected(SelectionEvent e) {
		}
	};
	
	private static final SelectionListener schemeSelectionListener = new SelectionListener() {
		@Override
		public void widgetSelected(SelectionEvent e) {
			Preferences.setDefaultFeatureNameFormat((Integer) ((Button) e.getSource()).getData());
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
		container.setLayout(new FillLayout(SWT.VERTICAL));
		
		final Group completionGroup = new Group(container, SWT.SHADOW_IN);
	    completionGroup.setText("Configuration Coloring");
	    completionGroup.setLayout(new RowLayout(SWT.VERTICAL));
	    completionGroup.setToolTipText("The configuration editor provides feature highlighting for invalid configurations in oder to find valid configurations.");
	    final Button noneButton = new Button(completionGroup, SWT.RADIO);
	    final Button openClauseButton = new Button(completionGroup, SWT.RADIO);
	    final Button contradictionButton = new Button(completionGroup, SWT.RADIO);
	    
	    noneButton.setData(Preferences.COMPLETION_NONE);
	    openClauseButton.setData(Preferences.COMPLETION_OPEN_CLAUSES);
	    contradictionButton.setData(Preferences.COMPLETION_ONE_CLICK);
	    
	    noneButton.setText("None");
	    openClauseButton.setText("Check open clauses (Faster results)");
	    contradictionButton.setText("Check contradiction (Better results)");

	    noneButton.setToolTipText("Diseable the functionality (Yields best performance for large feature models).");
	    openClauseButton.setToolTipText("Looks for open clauses in the CNF representation of the feature model and highlights the corresponding features.");
	    contradictionButton.setToolTipText("Tries to find features which lead to a valid configuration by solving a satisfiability problem.");
	    
	    switch (Preferences.getDefaultCompletion()) {
    	case Preferences.COMPLETION_NONE:
	    	noneButton.setSelection(true);
	    	break;
    	case Preferences.COMPLETION_OPEN_CLAUSES:
    		openClauseButton.setSelection(true);
	    	break;
    	case Preferences.COMPLETION_ONE_CLICK:
    		contradictionButton.setSelection(true);
	    	break;
	    }
		
	    final Group schemeGroup = new Group(container, SWT.SHADOW_IN);
	    schemeGroup.setText("Feature name scheme");
	    schemeGroup.setLayout(new RowLayout(SWT.VERTICAL));
	    final Button useShortFeatureNames = new Button(schemeGroup, SWT.RADIO);
	    final Button useLongFeatureName = new Button(schemeGroup, SWT.RADIO);
	    
	    useShortFeatureNames.setData(Preferences.SCHEME_SHORT);
	    useLongFeatureName.setData(Preferences.SCHEME_LONG);
	    
	    useShortFeatureNames.setText("Use short feature names");
	    useLongFeatureName.setText("Use long feature names");
	    
	    switch (Preferences.getDefaultFeatureNameScheme()) {
    	case Preferences.SCHEME_SHORT:
    		useShortFeatureNames.setSelection(true);
	    	break;
    	case Preferences.SCHEME_LONG:
    		useLongFeatureName.setSelection(true);
	    	break;
	    }
	    
	    noneButton.addSelectionListener(completionSelectionListener);
	    openClauseButton.addSelectionListener(completionSelectionListener);
	    contradictionButton.addSelectionListener(completionSelectionListener);
	    
	    useShortFeatureNames.addSelectionListener(schemeSelectionListener);
	    useLongFeatureName.addSelectionListener(schemeSelectionListener);
	    
		return container;
	}
}
