/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.statistics.ui.helper;

import guidsl.Paren;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.content.IContentDescription;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.IEditorDescriptor;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.progress.UIJob;
import org.eclipse.ui.texteditor.ITextEditor;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.abstr.AbstractClassFragment;
import de.ovgu.featureide.core.signature.abstr.AbstractSignature;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.ConfigParentNode;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes.AbstractSortModeNode;
import de.ovgu.featureide.ui.statistics.ui.ConfigDialog;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.TreeItem;

/**
 * Simple listener for the treeview.
 * 
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public class TreeClickListener implements IDoubleClickListener {

	private TreeViewer view;

	public TreeClickListener(TreeViewer view) {
		super();
		this.view = view;
//		this.viewer = view;
	}

	/**
	 * Performs actions depending on the type of the clicked note e.g. opening a
	 * dialog for {@link ConfigParentNode.ConfigNode} or
	 * expanding/collapsing nodes(default operation).
	 * 
	 */
	@Override
	public void doubleClick(DoubleClickEvent event) {
		Object[] selectedObjects = ((TreeSelection) event.getSelection()).toArray();
		
		if(selectedObjects.length == 1 && selectedObjects[0] instanceof Parent && ((Parent) selectedObjects[0]).getValue() instanceof FSTRole){
			FSTRole role = (FSTRole)((Parent) selectedObjects[0]).getValue();
			IFile file = role.getFile();
			System.out.println();
		}
		
		
		for (Object selected : selectedObjects) {
			if (selected instanceof ConfigParentNode.ConfigNode) {
				handleConfigNodes(event, selected);
				System.out.println("ConfigParentNode geklickt");//löschen
			} else if (selected instanceof AbstractSortModeNode && view.getExpandedState(selected)) {
				final AbstractSortModeNode sortNode = ((AbstractSortModeNode) selected);
				sortNode.setSortByValue(!sortNode.isSortByValue());

				UIJob job = new UIJob("resort node") {
					@Override
					public IStatus runInUIThread(IProgressMonitor monitor) {
						view.refresh(sortNode);
						return Status.OK_STATUS;
					}
				};
				job.setPriority(Job.INTERACTIVE);
				job.schedule();
				System.out.println("AbstractSortModeNode und view.getExpandedState");//löschen
			} else if (selected instanceof Parent && ((Parent) selected).hasChildren()) {
				view.setExpandedState(selected, !view.getExpandedState(selected));
				System.out.println("Parent und Parent hat Kinder");//löschen
			} else if (selected instanceof Parent && !((Parent) selected).hasChildren() && ((Parent) selected).getParent().getParent() != null) {

				//Unser Müll
//
//				final IFeatureProject featureProject = (IFeatureProject) CorePlugin.getFeatureProjects().toArray()[0];//getFeatureProject(IResource.);
//				//aktuelles Featurepro???????????
//				final IFeatureProject featureProject = CorePlugin.getFeatureProject((IResource) viewer.getInput());
				
//				final FSTModel model = featureProject.getFSTModel();
//				final ProjectSignatures signatures = featureProject.getProjectSignatures();
//				
//				//hier wird der godfather gesucht
//				if (model != null && signatures != null) {
//					AbstractSignature parent = sig;
//					while (parent.getParent() != null) {
//						parent = parent.getParent();
//					}
//				
//				final String fullName = parent.getFullName();
//				final String fileName = (fullName.startsWith(".")) ? fullName.substring(1) : fullName.replace('.', '/');
//	
//				//merkt sich die datei
//				final IFile iFile = model.getFeature(signatures.getFeatureName(featureID)).getRole(fileName + ".java").getFile();
//	
//				
//				if (iFile.isAccessible()) {
//					final IWorkbench workbench = PlatformUI.getWorkbench();
//					try {
//						final IContentDescription description = iFile.getContentDescription();
//						final IEditorDescriptor desc = workbench.getEditorRegistry().getDefaultEditor(iFile.getName(),
//								(description != null) ? description.getContentType() : null);
//						final IWorkbenchPage activePage = workbench.getActiveWorkbenchWindow().getActivePage();
//						IEditorPart editorPart = activePage.findEditor(new FileEditorInput(iFile));
//						if (editorPart == null) {
//							editorPart = activePage.openEditor(new FileEditorInput(iFile), (desc != null) ? desc.getId() : "org.eclipse.ui.DefaultTextEditor");
//						}
//						final int dataIndex = sig.hasFeature(featureID);
//						scrollToLine(editorPart, (dataIndex > -1) ? sig.getFeatureData()[dataIndex].getLineNumber() : 1);
//					} catch (CoreException e) {
//						UIPlugin.getDefault().logError(e);
//					}
//				}
				
				
				
				
				
				
				
				
				
				
				
				
				
				
				
				System.out.println(selected.getClass().getName() + " " + selected.toString() + " ");
				System.out.println("Viewer initiieren");
//				initViewer();
				System.out.println("Viewer ok");
				System.out.println("SelectionChangeListener zuweisen");//löschen
				//viewer.addSelectionChangedListener(sListener);
				//selected.höre auf unseren listener

			}
		}
	}

	/**
	 * Opens a dialog to start the calculation corresponding to the clicked
	 * config-node - but only if their isn't already a calculation in progress.
	 * 
	 */
	private void handleConfigNodes(DoubleClickEvent event, Object selected) {
		ConfigParentNode.ConfigNode clickedNode = (ConfigParentNode.ConfigNode) selected;
		if (!clickedNode.isCalculating()) {
			ConfigDialog dial = new ConfigDialog(event.getViewer().getControl().getShell(), clickedNode.getDescription());
			if (dial.open() == ConfigDialog.OK) {
				clickedNode.calculate(dial.getTimeout(), dial.getPriority());
			}
		}
	}

	//versuch
//	protected TreeViewer viewer;//wer soll tun --> woher infos?
//	
//	public void initViewer() {
//		
//		viewer.addSelectionChangedListener(sListener);
//	}
	


	//	public void initTreeViewer(TreeViewer viewer) {
	//		this.viewer = viewer;
	//		viewer.addSelectionChangedListener(sListener);
	//	}

//	private ISelectionChangedListener sListener = new ISelectionChangedListener() {
//		@Override
//		public void selectionChanged(SelectionChangedEvent event) {
//			System.out.println("SelectionCangeListener wird aufgerufen");//löschen
//			if (viewer.getInput() != null) {
//				Object selection = ((IStructuredSelection) viewer.getSelection()).getFirstElement();
////				if (!(viewer.getInput() instanceof IResource)) {
////					System.out.println("raussprung");//löschen
////					return;
////				}
//				System.out.println("vor featureproject angelegt");//löschen
//				final IFeatureProject featureProject = CorePlugin.getFeatureProject((IResource) viewer.getInput());   //VERURSACHT NUR PROBLEME!!!!!!!!!!!!!!!!!!
//				System.out.println("nach featureproject angelegt");//löschen
//				if (selection instanceof AbstractClassFragment) {
//					final AbstractSignature sig = ((AbstractClassFragment) selection).getSignature();
//					openEditor(sig, featureProject, sig.getFeatureData()[0].getId());
//				} else if (selection instanceof AbstractSignature) {
//					final AbstractSignature sig = (AbstractSignature) selection;
//					openEditor(sig, featureProject, sig.getFeatureData()[0].getId());
//				} else if (selection instanceof Feature) {
//					final ProjectSignatures signatures = featureProject.getProjectSignatures();
//					if (signatures != null) {
//						final TreeItem decl = viewer.getTree().getSelection()[0].getParentItem();
//						openEditor((AbstractSignature) decl.getData(), featureProject, signatures.getFeatureID(((Feature) selection).getName()));
//					}
//				}
//			}
//		}
//
//	};
//
//	private void openEditor(AbstractSignature sig, IFeatureProject featureProject, int featureID) {
//		System.out.println("OpenEditor wird aufgerufent");//löschen
//		final FSTModel model = featureProject.getFSTModel();
//		final ProjectSignatures signatures = featureProject.getProjectSignatures();
//		
//		//hier wird der godfather gesucht
//		if (model != null && signatures != null) {
//			AbstractSignature parent = sig;
//			while (parent.getParent() != null) {
//				parent = parent.getParent();
//			}
//
//	//Verzeichnis benennen
//			final String fullName = parent.getFullName();
//			final String fileName = (fullName.startsWith(".")) ? fullName.substring(1) : fullName.replace('.', '/');
//
//			//merkt sich die datei
//			final IFile iFile = model.getFeature(signatures.getFeatureName(featureID)).getRole(fileName + ".java").getFile();
//
//			
//			if (iFile.isAccessible()) {
//				final IWorkbench workbench = PlatformUI.getWorkbench();
//				try {
//					final IContentDescription description = iFile.getContentDescription();
//					final IEditorDescriptor desc = workbench.getEditorRegistry().getDefaultEditor(iFile.getName(),
//							(description != null) ? description.getContentType() : null);
//					final IWorkbenchPage activePage = workbench.getActiveWorkbenchWindow().getActivePage();
//					IEditorPart editorPart = activePage.findEditor(new FileEditorInput(iFile));
//					if (editorPart == null) {
//						editorPart = activePage.openEditor(new FileEditorInput(iFile), (desc != null) ? desc.getId() : "org.eclipse.ui.DefaultTextEditor");
//					}
//					final int dataIndex = sig.hasFeature(featureID);
//					scrollToLine(editorPart, (dataIndex > -1) ? sig.getFeatureData()[dataIndex].getLineNumber() : 1);
//				} catch (CoreException e) {
//					UIPlugin.getDefault().logError(e);
//				}
//			}
//		}
//	}
//
//	public static void scrollToLine(IEditorPart editorPart, int lineNumber) {
//		if (!(editorPart instanceof ITextEditor) || lineNumber <= 0) {
//			return;
//		}
//		final ITextEditor editor = (ITextEditor) editorPart;
//		final IDocument document = editor.getDocumentProvider().getDocument(editor.getEditorInput());
//		if (document != null) {
//			IRegion lineInfo = null;
//			try {
//				lineInfo = document.getLineInformation(lineNumber - 1);
//			} catch (BadLocationException e) {
//			}
//			if (lineInfo != null) {
//				editor.selectAndReveal(lineInfo.getOffset(), lineInfo.getLength());
//			}
//		}
//	}

}
