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
package de.ovgu.featureide.ui.preferences;

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

import de.ovgu.featureide.core.preferences.ContextOutlinePreference;

public class ContextOutlinePreferencePage extends PreferencePage implements IWorkbenchPreferencePage {
	
	private SelectionListener selectionListener = new SelectionListener() {
		@Override
		public void widgetSelected(SelectionEvent e) {
			ContextOutlinePreference.getInstance().setCurrentValue((Integer) ((Button) e.getSource()).getData());
		}
		
		@Override
		public void widgetDefaultSelected(SelectionEvent e) {
		}
	};

	public ContextOutlinePreferencePage() {
	}

	public ContextOutlinePreferencePage(String title) {
		super(title);
	}

	public ContextOutlinePreferencePage(String title, ImageDescriptor image) {
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
	    configGroup.setText("Context Outline Mode");
	    configGroup.setLayout(new RowLayout(SWT.VERTICAL));
	    final Button noneButton = new Button(configGroup, SWT.RADIO);
	    final Button contextButton = new Button(configGroup, SWT.RADIO);
	    final Button coreButton = new Button(configGroup, SWT.RADIO);
	    final Button configurationButton = new Button(configGroup, SWT.RADIO);
	    
	    noneButton.setData(ContextOutlinePreference.CONTEXTOUTLINE_NONE);
	    contextButton.setData(ContextOutlinePreference.CONTEXTOUTLINE_CONTEXT);
	    coreButton.setData(ContextOutlinePreference.CONTEXTOUTLINE_CORE);
	    configurationButton.setData(ContextOutlinePreference.CONTEXTOUTLINE_CONFIGURATION);
	    
	    noneButton.setText("None");
	    contextButton.setText("Current Context");
	    coreButton.setText("Core Features");
	    configurationButton.setText("Current Configuration");
	    
	    switch (ContextOutlinePreference.getInstance().getCurrentValue()) {
    	case ContextOutlinePreference.CONTEXTOUTLINE_NONE:
	    	noneButton.setSelection(true);
	    	break;
    	case ContextOutlinePreference.CONTEXTOUTLINE_CONTEXT:
    		contextButton.setSelection(true);
	    	break;
    	case ContextOutlinePreference.CONTEXTOUTLINE_CORE:
    		coreButton.setSelection(true);
	    	break;
    	case ContextOutlinePreference.CONTEXTOUTLINE_CONFIGURATION:
    		configurationButton.setSelection(true);
	    	break;
	    }
	    
	    noneButton.addSelectionListener(selectionListener);
	    contextButton.addSelectionListener(selectionListener);
	    coreButton.addSelectionListener(selectionListener);
	    configurationButton.addSelectionListener(selectionListener);
	    
		return container;
	}
}
