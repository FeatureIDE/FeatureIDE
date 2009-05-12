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
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;

import featureide.fm.core.FeatureModel;
import featureide.fm.core.io.UnsupportedModelException;
import featureide.fm.core.io.guidsl.FeatureModelReader;
import featureide.fm.core.io.xml.XmlFeatureModelWriter;

/**
 * TODO description
 * 
 * @author Fabian Wielgorz
 */
public class ExportXmlAction implements IObjectActionDelegate {

private ISelection selection;
	
	@Override
	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
		
	}

	@Override
	@SuppressWarnings("unchecked")
	public void run(IAction action) {
		if (selection instanceof IStructuredSelection) {
			for (Iterator it = ((IStructuredSelection) selection).iterator(); 
					it.hasNext();) {
				Object element = it.next();
				IFile inputFile = null;
				if (element instanceof IFile) {
					inputFile = (IFile) element;
				} else if (element instanceof IAdaptable) {
					inputFile = (IFile) ((IAdaptable) element).getAdapter(
							IFile.class);
				}
				if (inputFile != null) {
					try {
						FileDialog fileDialog = new FileDialog(new Shell(), 
								SWT.SAVE);
						fileDialog.setFileName("model.xml");
						fileDialog.setOverwrite(true);
						File outputFile = new File(fileDialog.open());
						FeatureModel fm = new FeatureModel();
						FeatureModelReader fmReader = new FeatureModelReader(fm);		
						fmReader.readFromFile(inputFile);
						XmlFeatureModelWriter xmlWriter = 
							new XmlFeatureModelWriter(fm);
						xmlWriter.writeToFile(outputFile);
						inputFile.getProject().refreshLocal(
								IResource.DEPTH_INFINITE, null);  
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
