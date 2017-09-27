/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.wizards;

import org.eclipse.jface.wizard.IWizard;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;

/**
 * A dialog page to specify a feature name.
 *
 * @author Sebastian Krieter
 */
public abstract class AbstractWizardPage extends WizardPage {

	protected class KeyPressedListener implements KeyListener {

		public KeyPressedListener() {}

		@Override
		public void keyPressed(KeyEvent e) {}

		@Override
		public void keyReleased(KeyEvent e) {
			updatePage();
		}
	}

	protected AbstractWizard abstractWizard;
	private boolean dirty = true;

	protected AbstractWizardPage(String name) {
		super(name);
		super.setPageComplete(false);
	}

	@Override
	public void setWizard(IWizard newWizard) {
		super.setWizard(newWizard);
		if (newWizard instanceof AbstractWizard) {
			abstractWizard = (AbstractWizard) newWizard;
		} else {
			abstractWizard = null;
		}
	}

	public final void updatePage() {
		final String message = checkPage();
		setErrorMessage(message);
		dirty = true;
		if (message == null) {
			setPageComplete(true);
		} else {
			removeData();
		}
	}

	public final void saveData() {
		if (dirty) {
			if (abstractWizard != null) {
				putData();
			}
			dirty = false;
		}
	}

	protected abstract void putData();

	protected void removeData() {}

	protected String checkPage() {
		return null;
	}
}
