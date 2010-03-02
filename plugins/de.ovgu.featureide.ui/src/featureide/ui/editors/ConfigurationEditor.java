/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
package featureide.ui.editors;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ITreeSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorPart;

import featureide.core.CorePlugin;
import featureide.core.IFeatureProject;
import featureide.fm.core.FeatureModel;
import featureide.fm.core.PropertyConstants;
import featureide.fm.core.configuration.Configuration;
import featureide.fm.core.configuration.ConfigurationReader;
import featureide.fm.core.configuration.ConfigurationWriter;
import featureide.fm.core.configuration.SelectableFeature;
import featureide.fm.core.configuration.Selection;
import featureide.fm.ui.editors.configuration.ConfigurationContentProvider;
import featureide.fm.ui.editors.configuration.ConfigurationLabelProvider;
import featureide.ui.UIPlugin;

/**
 * ConfiguratonEitor displays the Equation File. 
 * 
 * @author Constanze Adler
 * @author Christian Becker
 */

public class ConfigurationEditor extends EditorPart implements
		PropertyChangeListener, PropertyConstants, IResourceChangeListener {

	private TreeViewer viewer;

	private Configuration configuration;

	private boolean dirty = false;
	
	private boolean closeEditor;

	private IDoubleClickListener listener = new IDoubleClickListener() {

		public void doubleClick(DoubleClickEvent event) {
			Object object = ((ITreeSelection) event.getSelection())
					.getFirstElement();
			if (object instanceof SelectableFeature) {
				final SelectableFeature feature = (SelectableFeature) object;
				changeSelection(feature);
			}
		}
	};

	private IFile file;

	@Override
	public void doSave(IProgressMonitor monitor) {
		try {
			new ConfigurationWriter(configuration).saveToFile(file);
			dirty = false;
			firePropertyChange(IEditorPart.PROP_DIRTY);
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}

	@Override
	public void doSaveAs() {
	}

	@Override
	public void init(IEditorSite site, IEditorInput input)
			throws PartInitException {
		setSite(site);
		setInput(input);
		ResourcesPlugin.getWorkspace().addResourceChangeListener(this); 

		file = (IFile) input.getAdapter(IFile.class);
		UIPlugin.getDefault().logInfo("file: " + file);
		setPartName(file.getName());

		IFeatureProject featureProject = CorePlugin.getProjectData(file);
		FeatureModel featureModel = featureProject.getFeatureModel();
		featureModel.addListener(this);
		configuration = new Configuration(featureModel, true);
		try {
			dirty = !new ConfigurationReader(configuration).readFromFile(file);
			if (!dirty)
				dirty = !configuration.validManually();
		} catch (Exception e) {
			e.printStackTrace();
		}
		firePropertyChange(IEditorPart.PROP_DIRTY);
	}

	@Override
	public boolean isDirty() {
		return dirty;
	}

	@Override
	public boolean isSaveAsAllowed() {
		return false;
	}

	@Override
	public void createPartControl(Composite parent) {
		viewer = new TreeViewer(parent, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);
		viewer.addDoubleClickListener(listener);
		viewer.getTree().addKeyListener(new KeyListener() {
			
			public void keyPressed(KeyEvent e) {
				if (e.character == ' ') {
					if (viewer.getSelection() instanceof ITreeSelection) {
						final ITreeSelection tree = (ITreeSelection) viewer
								.getSelection();
						Object object = tree.getFirstElement();
						if (object instanceof SelectableFeature) {
							final SelectableFeature feature = (SelectableFeature) object;
							changeSelection(feature);
						}
					}
				}
			}

			
			public void keyReleased(KeyEvent e) {

			}
		});
		viewer.setContentProvider(new ConfigurationContentProvider());
		viewer.setLabelProvider(new ConfigurationLabelProvider());
		viewer.setInput(configuration);
		viewer.expandAll();

	}

	@Override
	public void setFocus() {
		viewer.getControl().setFocus();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @seejava.beans.PropertyChangeListener#propertyChange(java.beans.
	 * PropertyChangeEvent)
	 */

	public void propertyChange(PropertyChangeEvent evt) {
		try {
			new ConfigurationWriter(configuration).saveToFile(file);
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}

	/**
	 * @param The feature which change the selection status
	 * 
	 */
	protected void changeSelection(SelectableFeature feature) {
		if (feature.getAutomatic() == Selection.UNDEFINED) {
			// set to the next value
			if (feature.getManual() == Selection.UNDEFINED)
				set(feature, Selection.SELECTED);
			else if (feature.getManual() == Selection.SELECTED)
				set(feature, Selection.UNSELECTED);
			else
				// case: unselected
				set(feature, Selection.UNDEFINED);
			if (!dirty) {
				dirty = true;
				firePropertyChange(IEditorPart.PROP_DIRTY);
			}
			viewer.refresh();
		}
	}

	protected void set(SelectableFeature feature, Selection selection) {
		configuration.setManual(feature, selection);
	}

	
	/* (non-Javadoc)
	 * @see org.eclipse.core.resources.IResourceChangeListener#resourceChanged(org.eclipse.core.resources.IResourceChangeEvent)
	 */
	public void resourceChanged(IResourceChangeEvent event) {
		
		if (event.getResource().getType() == IResource.PROJECT)
			 closeEditor = true;
		final IEditorInput input=getEditorInput();
		if (!( input instanceof IFileEditorInput ))
		           return;
		final IFile jmolfile=((IFileEditorInput)input).getFile();
		 
		/*
	     * Closes editor if resource is deleted
	      */
	       if ((event.getType() == IResourceChangeEvent.POST_CHANGE) && closeEditor) {
	          IResourceDelta rootDelta = event.getDelta();
	           //get the delta, if any, for the documentation directory
	           
	           final List<IResource> deletedlist = new ArrayList<IResource>();
	           
	           IResourceDelta docDelta = rootDelta.findMember(jmolfile.getFullPath());
	           if (docDelta != null){
	               IResourceDeltaVisitor visitor = new IResourceDeltaVisitor() {
	                   public boolean visit(IResourceDelta delta) {
	                      //only interested in removal changes
	                      if (((delta.getFlags() & IResourceDelta.REMOVED) == 0) && closeEditor){
	                          deletedlist.add( delta.getResource() );
	                      }
	                      return true;
	                   }
	                };
	                
	                try {
						docDelta.accept(visitor);
					} catch (CoreException e) {
						e.printStackTrace();
					}
	                
	           }
	               
	           if (deletedlist.size()>0 && deletedlist.contains( jmolfile )){
	        	   Display.getDefault().asyncExec(new Runnable() {
	                   public void run() {
	                       if (getSite()==null) 
	                           return;
	                       if (getSite().getWorkbenchWindow()==null) 
	                           return;
	                       
	                       IWorkbenchPage[] pages = getSite().getWorkbenchWindow()
	                                                         .getPages();
	                     
	                       for (int i = 0; i<pages.length; i++) {
	                               IEditorPart editorPart
	                                 = pages[i].findEditor(input);
	                               pages[i].closeEditor(editorPart,true);
	                       }
	                   }
	               });
	           }
	           

	           
	       }

	       /*
	        * Closes all editors with this editor input on project close.
	        */

		 
		 final IResource res = event.getResource();
		 if ((event.getType() == IResourceChangeEvent.PRE_CLOSE ) || closeEditor) {
			 Display.getDefault().asyncExec(new Runnable() {
				 public void run() {
					 if (getSite()==null)
						 return;
					 if (getSite().getWorkbenchWindow()==null)
						 return;
					 IWorkbenchPage[] pages = getSite().getWorkbenchWindow().getPages();
					 for (int i = 0; i<pages.length; i++) {
						 if ( jmolfile.getProject().equals( res )) {
							 IEditorPart editorPart = pages[i].findEditor(input);
							 pages[i].closeEditor(editorPart,true);
		                 }
					 }
				 }
			 });
		 }

	
		
	}
}
