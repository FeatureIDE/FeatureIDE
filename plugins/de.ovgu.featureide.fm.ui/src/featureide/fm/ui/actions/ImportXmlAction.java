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
package featureide.fm.ui.actions;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Iterator;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;

import featureide.fm.core.FeatureModel;
import featureide.fm.core.io.UnsupportedModelException;
import featureide.fm.core.io.guidsl.FeatureModelWriter;
import featureide.fm.core.io.xml.XmlFeatureModelReader;
import featureide.fm.ui.editors.FeatureModelEditor;

/**
 * TODO description
 * 
 * @author Fabian Wielgorz
 */
public class ImportXmlAction implements IObjectActionDelegate {

private ISelection selection;
	
	private FeatureModelEditor featureModelEditor;
	
	@Override
	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
		featureModelEditor = (targetPart instanceof FeatureModelEditor) ? 
				(FeatureModelEditor) targetPart : null;
	}

	@Override
	@SuppressWarnings("unchecked")
	public void run(IAction action) {
		if (selection instanceof IStructuredSelection) {
			for (Iterator it = ((IStructuredSelection) selection).iterator(); 
					it.hasNext();) {
				Object element = it.next();
				IFile outputFile = null;
				if (element instanceof IFile) {
					outputFile = (IFile) element;
				} else if (element instanceof IAdaptable) {
					outputFile = (IFile) ((IAdaptable) element).getAdapter(
							IFile.class);
				}
				if (outputFile != null) {
					try {
						MessageDialog.openWarning(new Shell(), "Warning!",
								"This will overide the current model! " +
								"Can't be undone!");
						FileDialog fileDialog = new FileDialog(new Shell(), 
								SWT.OPEN);
						fileDialog.setOverwrite(false);
						File inputFile = new File(fileDialog.open());
						if (inputFile == null) return;
						while (!inputFile.exists()) {
							MessageDialog.openInformation(new Shell(), "File " +
									"not Found", "Specified file wasn't found");
							inputFile = new File(fileDialog.open());
							if (inputFile == null) return;
						}							
						FeatureModel fm = new FeatureModel();
						XmlFeatureModelReader xmlReader = 
							new XmlFeatureModelReader(fm);		
						xmlReader.readFromFile(inputFile);
						FeatureModelWriter fmWriter = new FeatureModelWriter(fm);
						fmWriter.writeToFile(outputFile);
						outputFile.getProject().refreshLocal(
								IResource.DEPTH_INFINITE, null);
						if (featureModelEditor != null) {
							featureModelEditor.updateDiagramFromTextEditor();
						}
					} catch (FileNotFoundException e) {
						e.printStackTrace();
					} catch (UnsupportedModelException e) {
						e.printStackTrace();
					} catch (CoreException e) {
						e.printStackTrace();
					}			
				}
			}
		}
	}

	@Override
	public void selectionChanged(IAction action, ISelection selection) {
		this.selection = selection;
	}
}
