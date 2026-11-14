/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.projectExplorer.packages;

import java.net.MalformedURLException;
import java.net.URL;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.ui.IViewReference;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ISetSelectionTarget;

/**
 * Helpers for the wizards that create packages and classes in feature folders.
 *
 * @author Philipp Hehnle
 */
final class FeatureWizardSupport {

	private FeatureWizardSupport() {}

	/**
	 * @return the location for new Java elements from the first selected element, or <code>null</code>.
	 */
	static FeatureJavaLocation getLocation(IStructuredSelection selection) {
		return ((selection == null) || selection.isEmpty()) ? null : FeatureJavaLocation.of(selection.getFirstElement());
	}

	/**
	 * @return the banner image of a JDT wizard, e.g. <code>newpack_wiz.png</code>, or <code>null</code> if JDT does not provide it.
	 */
	static ImageDescriptor getJdtWizardBanner(String fileName) {
		try {
			return ImageDescriptor.createFromURL(new URL("platform:/plugin/org.eclipse.jdt.ui/icons/full/wizban/" + fileName));
		} catch (final MalformedURLException e) {
			return null;
		}
	}

	/**
	 * Shows the status of a validation on the wizard page and returns whether the page is complete.
	 */
	static boolean showStatus(WizardPage page, IStatus status) {
		if (status.getSeverity() == IStatus.ERROR) {
			page.setErrorMessage(status.getMessage());
			page.setMessage(null);
			return false;
		}
		page.setErrorMessage(null);
		page.setMessage(status.getSeverity() == IStatus.WARNING ? status.getMessage() : null,
				status.getSeverity() == IStatus.WARNING ? IMessageProvider.WARNING : IMessageProvider.NONE);
		return true;
	}

	/**
	 * Selects and reveals the element in the views of the active page that support it, e.g. the Project Explorer.
	 */
	static void selectAndReveal(Object element) {
		final IWorkbenchWindow window = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		final IWorkbenchPage page = (window != null) ? window.getActivePage() : null;
		if (page == null) {
			return;
		}
		final StructuredSelection selection = new StructuredSelection(element);
		for (final IViewReference reference : page.getViewReferences()) {
			final IWorkbenchPart part = reference.getPart(false);
			if (part instanceof ISetSelectionTarget) {
				((ISetSelectionTarget) part).selectReveal(selection);
			}
		}
	}
}
