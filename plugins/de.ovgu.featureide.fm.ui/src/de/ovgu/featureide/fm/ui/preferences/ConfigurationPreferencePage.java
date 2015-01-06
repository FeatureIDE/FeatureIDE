/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
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

import de.ovgu.featureide.fm.core.preferences.ConfigurationPreference;

public class ConfigurationPreferencePage extends PreferencePage implements
		IWorkbenchPreferencePage {
	
	private SelectionListener selectionListener = new SelectionListener() {
		@Override
		public void widgetSelected(SelectionEvent e) {
			ConfigurationPreference.getInstance().setCurrentValue((Integer) ((Button) e.getSource()).getData());
		}
		
		@Override
		public void widgetDefaultSelected(SelectionEvent e) {
		}
	};

	public ConfigurationPreferencePage() {
	}

	public ConfigurationPreferencePage(String title) {
		super(title);
	}

	public ConfigurationPreferencePage(String title, ImageDescriptor image) {
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
		
		final Group configGroup = new Group(container, SWT.SHADOW_IN);
	    configGroup.setText("Configuration Coloring");
	    configGroup.setLayout(new RowLayout(SWT.VERTICAL));
	    configGroup.setToolTipText("The configuration editor provides feature highlighting for invalid configurations in oder to find valid configurations.");
	    final Button noneButton = new Button(configGroup, SWT.RADIO);
	    final Button openClauseButton = new Button(configGroup, SWT.RADIO);
	    final Button contradictionButton = new Button(configGroup, SWT.RADIO);
	    
	    noneButton.setData(ConfigurationPreference.COMPLETION_NONE);
	    openClauseButton.setData(ConfigurationPreference.COMPLETION_OPEN_CLAUSES);
	    contradictionButton.setData(ConfigurationPreference.COMPLETION_ONE_CLICK);
	    
	    noneButton.setText("None");
	    openClauseButton.setText("Check open clauses (Faster results)");
	    contradictionButton.setText("Check contradiction (Better results)");

	    noneButton.setToolTipText("Do not use this functionality (Yields best performance for large feature models).");
	    openClauseButton.setToolTipText("Looks for open clauses in the CNF representation of the feature model and highlights the corresponding features.");
	    contradictionButton.setToolTipText("Tries to find features which lead to a valid configuration by solving a satisfiability problem.");
	    
	    switch (ConfigurationPreference.getInstance().getCurrentValue()) {
    	case ConfigurationPreference.COMPLETION_NONE:
	    	noneButton.setSelection(true);
	    	break;
    	case ConfigurationPreference.COMPLETION_OPEN_CLAUSES:
    		openClauseButton.setSelection(true);
	    	break;
    	case ConfigurationPreference.COMPLETION_ONE_CLICK:
    		contradictionButton.setSelection(true);
	    	break;
	    }
	    
	    noneButton.addSelectionListener(selectionListener);
	    openClauseButton.addSelectionListener(selectionListener);
	    contradictionButton.addSelectionListener(selectionListener);
	    
		return container;
	}
}
