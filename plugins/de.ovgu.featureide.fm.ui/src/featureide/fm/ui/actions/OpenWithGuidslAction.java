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

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Iterator;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;

import featureide.fm.core.FMCorePlugin;

/**
 * Opens the currently selected feature model with GUIDSL.
 * 
 * @author Thomas Thuem
 */
public class OpenWithGuidslAction implements IObjectActionDelegate {

	private ISelection selection;

	public OpenWithGuidslAction() {
	}

	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
	}

	public void selectionChanged(IAction action, ISelection selection) {
		this.selection = selection;
	}

	@SuppressWarnings("unchecked")
	public void run(IAction action) {
		if (selection instanceof IStructuredSelection) {
			for (Iterator it = ((IStructuredSelection) selection).iterator(); it.hasNext();) {
				Object element = it.next();
				IFile file = null;
				if (element instanceof IFile) {
					file = (IFile) element;
				} else if (element instanceof IAdaptable) {
					file = (IFile) ((IAdaptable) element).getAdapter(IFile.class);
				}
				if (file != null) {
					openWithGuidsl(file);
				}
			}
		}
	}
	
	private void openWithGuidsl(IFile modelfile) {
		try {
			File pathfile = FMCorePlugin.getDefault().getStateLocation().append("guidslpath.txt").toFile();
			String guidslJar = "";
			boolean newLocation = false;
			if (pathfile.exists()) {
		        BufferedReader reader = new BufferedReader(new FileReader(pathfile));
		        guidslJar = reader.readLine();
		        reader.close();
			}
			while (guidslJar != null && !new File(guidslJar).exists()) {
				newLocation = true;
				FileDialog fd = new FileDialog(Display.getDefault().getActiveShell(), SWT.OPEN);
		        fd.setText("Locate the guidsl.jar file");
		        fd.setFilterExtensions(new String[] { "*.jar" });
		        fd.setFileName(guidslJar);
		        guidslJar = fd.open();
			}
			if (new File(guidslJar).exists()) {
				if (newLocation) {
					BufferedWriter writer = new BufferedWriter(new FileWriter(pathfile));
					writer.write(guidslJar + "\r\n");
					writer.close();
				}
				execProcess("java -jar \"" + guidslJar + "\" \"" + modelfile.getLocation().toOSString() + "\"", modelfile.getParent().getLocation().toFile());
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	private final boolean showOutputs = true;

	private void execProcess(String command, File dir) throws IOException {
        System.out.println("Starting process: " + command);
        Process process = Runtime.getRuntime().exec(command, null, dir);
        BufferedReader input = new BufferedReader(new InputStreamReader(process.getInputStream()));
        BufferedReader error = new BufferedReader(new InputStreamReader(process.getErrorStream()));
        
        long start = System.currentTimeMillis();
        int diff = 250;
        while (true) {
            try {
                String line;
                while ((line = input.readLine()) != null) {
                    if (showOutputs) {
                        System.out.println(">>>" + line);
                    }
                }
                while ((line = error.readLine()) != null) {
                    System.err.println(">>>" + line);
                }
                if (System.currentTimeMillis() - start > diff) {
                    start += diff;
                    System.out.print(".");
                }
                int exitValue = process.exitValue();
                System.out.println("...finished (exit=" + exitValue + ")!");
                if (exitValue != 0) {
                    throw new IOException(
                            "The process doesn't finish normally (exit=" + exitValue + ")!");
                }
                return;
            }
            catch (IllegalThreadStateException e) {
            }
        }
    }

}
