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
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ITreeSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorSite;
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

public class ConfigurationEditor extends EditorPart implements PropertyChangeListener, PropertyConstants{

	private TreeViewer viewer;

	private Configuration configuration;

	private boolean dirty = false;

	private IDoubleClickListener listener = new IDoubleClickListener() {

		public void doubleClick(DoubleClickEvent event) {
			Object object = ((ITreeSelection) event.getSelection())
					.getFirstElement();
			if (object instanceof SelectableFeature) {
				final SelectableFeature feature = (SelectableFeature) object;
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
		}

		private void set(SelectableFeature feature, Selection selection) {
			configuration.setManual(feature, selection);
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

		file = (IFile) input.getAdapter(IFile.class);
		UIPlugin.getDefault().logInfo("file: " + file);
		setPartName(file.getName());
		
		IFeatureProject featureProject = CorePlugin.getProjectData(file);
		FeatureModel featureModel = featureProject.getFeatureModel();
		System.out.println("Config "+featureModel.toString());
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
		viewer.setContentProvider(new ConfigurationContentProvider());
		viewer.setLabelProvider(new ConfigurationLabelProvider());
		
		viewer.setInput(configuration);
		viewer.expandAll();
		// viewer.expandAll();
	}

	@Override
	public void setFocus() {
		viewer.getControl().setFocus();
	}

	/* (non-Javadoc)
	 * @see java.beans.PropertyChangeListener#propertyChange(java.beans.PropertyChangeEvent)
	 */
	@Override
	public void propertyChange(PropertyChangeEvent evt) {
		try {
			new ConfigurationWriter(configuration).saveToFile(file);
		} catch (CoreException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

}
