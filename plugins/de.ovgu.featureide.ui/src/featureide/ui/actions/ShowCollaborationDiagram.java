/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package featureide.ui.actions;

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;

import featureide.core.CorePlugin;
import featureide.core.IFeatureProject;
import featureide.core.projectstructure.nodetypes.Visitor;
import featureide.ui.collaborationdiagram.CD_Diagram;
import featureide.ui.collaborationdiagram.CD_Vis;
import featureide.ui.collaborationdiagram.CollaborationVisitor;

/**
 * Our sample action implements workbench action delegate. The action proxy will
 * be created by the workbench and shown in the UI. When the user tries to use
 * the action, this delegate will be created and execution will be delegated to
 * it.
 * 
 * @see IWorkbenchWindowActionDelegate
 */
public class ShowCollaborationDiagram implements IWorkbenchWindowActionDelegate {

	// private IWorkbenchWindow window;
	//
	// /**
	// * The constructor.
	// */
	// public ShowCollaborationDiagram() {
	// }

	private IWorkbenchWindow window;

	/**
	 * The action has been activated. The argument of the method represents the
	 * 'real' action sitting in the workbench UI.
	 * 
	 * @see IWorkbenchWindowActionDelegate#run
	 */
	public void run(IAction action) {
		// MemoryTestBench memUsageTest = new MemoryTestBench();
		// memUsageTest.setMemUsageBefore(memUsageTest.memoryUsageWGarbageCol());

		/*
		 * Testing Execution Time
		 */
		IWorkbenchWindow editor = PlatformUI.getWorkbench()
				.getActiveWorkbenchWindow();
		FileEditorInput inputFile = (FileEditorInput) editor.getActivePage()
				.getActiveEditor().getEditorInput();
		IFeatureProject featureProject = CorePlugin.getProjectData(inputFile
				.getFile());
		Visitor visitor = new CollaborationVisitor();
		visitor.visitTree(featureProject.getProjectTree());
		CD_Diagram diagram = ((CollaborationVisitor) visitor)
				.getCollaborationDiagram();
		if (diagram == null)
			MessageDialog.openError(window.getShell(), "Visualization Error",
					"Data model for feature project "
							+ featureProject.getProject().getName()
							+ " not available.");
		else
			new CD_Vis(diagram);

	}

	/**
	 * Selection in the workbench has been changed. We can change the state of
	 * the 'real' action here if we want, but this can only happen after the
	 * delegate has been created.
	 * 
	 * @see IWorkbenchWindowActionDelegate#selectionChanged
	 */
	public void selectionChanged(IAction action, ISelection selection) {
	}

	/**
	 * We can use this method to dispose of any system resources we previously
	 * allocated.
	 * 
	 * @see IWorkbenchWindowActionDelegate#dispose
	 */
	public void dispose() {
	}

	/**
	 * We will cache window object in order to be able to provide parent shell
	 * for the message dialog.
	 * 
	 * @see IWorkbenchWindowActionDelegate#init
	 */
	public void init(IWorkbenchWindow window) {
		this.window = window;
	}

}