/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.ui.handlers;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;

import de.ovgu.featureide.fm.ui.handlers.base.ASelectionHandler;
import de.ovgu.featureide.ui.wizards.ConversionWizard;
import de.ovgu.featureide.ui.wizards.ImportFeatureHouseProjectWizard;

/**
 * Handler for the {@link ImportFeatureHouseProjectWizard}
 * 
 * @author Anna-Liisa Ahola
 */
public class ImportFeatureHouseProjectHandler extends ASelectionHandler implements SelectionListener{

	private Composite widgetSelectedParent;
	
	/**
	 * Default empty constructor
	 */
	public ImportFeatureHouseProjectHandler() {
	}
	
	/**
	 * Creates a specific instance of this handler.
	 * This constructor is used for the implementation of the
	 * Selection Listener interface
	 * @param parent
	 */
	public ImportFeatureHouseProjectHandler(Composite parent) {
		this.widgetSelectedParent = parent;
	}
	
	@Override
	protected boolean startAction(IStructuredSelection selection) {
		final ImportFeatureHouseProjectWizard wizard = new ImportFeatureHouseProjectWizard();
		wizard.init(null, selection);
		final WizardDialog dialog = new WizardDialog(Display.getCurrent().getActiveShell(), wizard);
		if (dialog.open() == Dialog.OK) {
			// ...
		}
		return false;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.handlers.base.ASelectionHandler#singleAction(java.lang.Object)
	 */
	@Override
	protected void singleAction(Object element) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see org.eclipse.swt.events.SelectionListener#widgetSelected(org.eclipse.swt.events.SelectionEvent)
	 */
	@Override
	public void widgetSelected(SelectionEvent e) {
		Button checkBox = (Button) e.getSource();
		if (checkBox.getSelection()) {
			for (Control child: widgetSelectedParent.getChildren()) {
				child.setVisible(true);
			}		
		} else {
			for (Control child: widgetSelectedParent.getChildren()) {
				if (child instanceof Button) {
					Button childButton = (Button) child;
					if (!childButton.equals(checkBox)) {
						child.setVisible(false);
					}
				} else {
					child.setVisible(false);
				}
			}
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.swt.events.SelectionListener#widgetDefaultSelected(org.eclipse.swt.events.SelectionEvent)
	 */
	@Override
	public void widgetDefaultSelected(SelectionEvent e) {
		
		
	}

}
