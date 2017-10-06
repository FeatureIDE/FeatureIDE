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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;


import static de.ovgu.featureide.fm.core.localization.StringTable.MANAGE_ATTRIBUTE;

import de.ovgu.featureide.fm.core.base.impl.FeatureAttribute;
import de.ovgu.featureide.fm.core.base.impl.FeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.ui.editors.ChangeFeatureDescriptionDialog;
import de.ovgu.featureide.fm.ui.editors.ConstraintDialog;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;

import static de.ovgu.featureide.fm.core.localization.StringTable.ADD_ATTRIBUTES;
import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_CONSTRAINT;
import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE_INCLUDING_SUBFEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.EXPORT_AS;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURE_DESCRIPTION;
import static de.ovgu.featureide.fm.core.localization.StringTable.PLEASE_ENTER_A_DESCRIPTION_FOR_FEATURE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.HERE_YOU_CAN_ADD_ATTRIBUTES;

import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.window.Window;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.actions.ActionFactory;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.io.EclipseFileSystem;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelFormat;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.ChangeFeatureDescriptionDialog;
import de.ovgu.featureide.fm.ui.editors.AddAttributeDialog;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ModelEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.ElementDeleteOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureTreeDeleteOperation;


public class AddAttributeAction extends Action  {
	
	private IFeatureModel featureModel;

	public AddAttributeAction(IFeatureModel featureMod) {
		super(MANAGE_ATTRIBUTE);
		this.featureModel = featureMod;
	}

	@Override
	public void run() {
//		Shell shell = new Shell(Display.getCurrent());
//		shell.setLayout(new FillLayout());
//		new AddAttributeDialog(shell, featureModel);
//		shell.open();
//		
//		while (!shell.isDisposed()) {
//			if (!Display.getCurrent().readAndDispatch()) Display.getCurrent().sleep();
//		}
		final Shell shell = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell();
		final AddAttributeDialog addAttributeDialog = new AddAttributeDialog(shell, featureModel);
		// inform ui to update
		if (addAttributeDialog.open() == Window.OK) {
			final IProject project = EclipseFileSystem.getResource(featureModel.getSourceFile()).getProject();
			try {
				project.touch(null);
				project.refreshLocal(IResource.DEPTH_INFINITE, new NullProgressMonitor());
			} catch (final CoreException e) {
				FMUIPlugin.getDefault().logError(e);
			}
		}
	}
}
