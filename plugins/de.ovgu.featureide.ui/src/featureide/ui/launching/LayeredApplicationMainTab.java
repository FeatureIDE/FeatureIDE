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
package featureide.ui.launching;

import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.util.Collection;
import java.util.LinkedList;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.jdt.debug.ui.launchConfigurations.JavaLaunchTab;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.dialogs.ElementListSelectionDialog;

import featureide.core.IFeatureProject;
import featureide.core.launching.LayeredApplicationLaunchConfigurationDelegate;

/**
 * This class is part of the launching package. It creates the
 * visible objects of the MainTab of the launch configuration.
 * 
 * @author Tom Brosch
 * @author Thomas Thuem
 *
 */
public class LayeredApplicationMainTab extends JavaLaunchTab implements ModifyListener {
	
	public static final String PROJECT_NAME = LayeredApplicationLaunchConfigurationDelegate.PROJECT_NAME;

	public static final String MAIN_CLASS = LayeredApplicationLaunchConfigurationDelegate.MAIN_CLASS;

	private Text projectEdit;

	private Button projectButton;

	private Text mainClassEdit;

	private Button mainClassButton;
	
	private IFeatureProject featureProject;

	public void createControl(Composite parent) {
		Composite comp = new Composite(parent, SWT.NONE);
		setControl(comp);
		GridLayout topLayout = new GridLayout();
		topLayout.numColumns = 1;
		comp.setLayout(topLayout);
		
		Group projectGroup = new Group(comp, SWT.NONE);
		projectGroup.setText("Project:");
		projectGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		GridLayout projGridLayout = new GridLayout();
		projGridLayout.numColumns = 2;
		projectGroup.setLayout(projGridLayout);
		projectEdit = new Text(projectGroup, SWT.BORDER);
		projectEdit.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		projectEdit.addModifyListener(this);
		projectButton = new Button(projectGroup, SWT.NONE);
		projectButton.setText("Browse");
		//use another type of listener here
		projectButton.addMouseListener(new MouseListener() {
			public void mouseDoubleClick(MouseEvent e) {
			}
			public void mouseDown(MouseEvent e) {
			}
			public void mouseUp(MouseEvent e) {
				if (e.button == 1)
					browseProjects();
			}
		});

		Group mainClassGroup = new Group(comp, SWT.NONE);
		mainClassGroup.setText("Main Class:");
		mainClassGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		GridLayout mainClassGridLayout = new GridLayout();
		mainClassGridLayout.numColumns = 2;
		mainClassGroup.setLayout(mainClassGridLayout);
		mainClassEdit = new Text(mainClassGroup, SWT.BORDER);
		mainClassEdit.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		mainClassEdit.addModifyListener(this);
		mainClassButton = new Button(mainClassGroup, SWT.NONE);
		mainClassButton.setText("Search");
		//use another type of listener here
		mainClassButton.addMouseListener(new MouseListener() {
			public void mouseDoubleClick(MouseEvent e) {
			}
			public void mouseDown(MouseEvent e) {
			}
			public void mouseUp(MouseEvent e) {
				if (e.button == 1)
					searchMainClass();
			}
		});
	}
	
	public void initializeFrom(ILaunchConfiguration configuration) {
		try {
			projectEdit.setText(configuration.getAttribute(PROJECT_NAME, "to be specified"));
			mainClassEdit.setText(configuration.getAttribute(MAIN_CLASS, "to be specified"));
			if( (featureProject = getProjectData()) == null )
				mainClassButton.setEnabled(false);
			else
				mainClassButton.setEnabled(true);
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}

	public void performApply(ILaunchConfigurationWorkingCopy configuration) {
		configuration.setAttribute(PROJECT_NAME, projectEdit.getText());
		configuration.setAttribute(MAIN_CLASS, mainClassEdit.getText());
		featureProject = getProjectData();
	}

	public boolean isValid(ILaunchConfiguration launchConfig) {
	    setErrorMessage(null);
	    featureProject = getProjectData();
	    mainClassButton.setEnabled(featureProject != null);
	    
	    if (featureProject == null) {
	    	setErrorMessage("Invalid project name");
	    	return false;
	    }
	    
	    if (!getMainClasses().contains(mainClassEdit.getText())) {
	    	setErrorMessage("Invalid main class");
	    	return false;
	    }
	    	
	    return true;
	}
	
	public void setDefaults(ILaunchConfigurationWorkingCopy configuration) {
		configuration.setAttribute(PROJECT_NAME, "default project");
		configuration.setAttribute(MAIN_CLASS, "default class");
	}
	
	public void modifyText(ModifyEvent e) {
		updateLaunchConfigurationDialog();
	}

	public String getName() {
		return "Main Tab";
	}

	public boolean canSave() {
		return isValid(null);
	}

	private IFeatureProject getProjectData() {
		for( IFeatureProject proj : featureide.core.CorePlugin.getFeatureProjects() )
	    	if( proj.getProjectName().equals(projectEdit.getText()))
	    		return proj;
		return null;
	}

	private void browseProjects() {
		ElementListSelectionDialog dialog = new ElementListSelectionDialog(
				null, new LabelProvider());
		Collection<IFeatureProject> featureProjectCollection = featureide.core.CorePlugin
				.getFeatureProjects();
		String[] elements = new String[featureProjectCollection.size()];
		int pos = 0;
		for (IFeatureProject featureProject : featureProjectCollection)
			elements[pos++] = featureProject.getProjectName();
		dialog.setElements(elements);
		dialog.setMessage("Select a project:");
		dialog.setTitle("Project selection");
		dialog.setMultipleSelection(false);
		dialog.open();
		if (dialog.getFirstResult() != null)
			projectEdit.setText(dialog.getFirstResult().toString());
	}
	
	private void searchMainClass() {
		ElementListSelectionDialog dialog = new ElementListSelectionDialog(
				null, new LabelProvider());
		LinkedList<String> classes = getMainClasses();
		dialog.setElements(classes.toArray());
		dialog.setMessage("Select the main class:");
		dialog.setTitle("Main Class Selection");
		dialog.setMultipleSelection(false);
		dialog.open();
		if (dialog.getFirstResult() != null)
			mainClassEdit.setText(dialog.getFirstResult().toString());
	}

	private LinkedList<String> getMainClasses() {
		LinkedList<String> classes = new LinkedList<String>();
		try {
			featureProject.getSourceFolder().accept(new MainClassVisitor(classes));
		} catch(CoreException e) {
			e.printStackTrace();
		}
		return classes;
	}

	private class MainClassVisitor implements IResourceVisitor {
		private LinkedList<String> classes;
		
		public MainClassVisitor(LinkedList<String> classes) {
			this.classes = classes;
		}
		
		public boolean visit(IResource resource) throws CoreException {
			if( resource instanceof IFile && resource.getFileExtension().equals("jak") ) {
				if (!containsMainMethod((IFile) resource))
					return true;

				String jakFilePath = resource.getRawLocation().toOSString();
				int start = jakFilePath.lastIndexOf(java.io.File.separatorChar) + 1;
				int end = jakFilePath.length() - ".jak".length();
				String className = jakFilePath.substring(start, end);
				if (!classes.contains(className))
					classes.add(className);
			}
			return true;
		}

		private boolean containsMainMethod(IFile file) {
			try {
				String text = getString(file);
				Pattern pattern = Pattern.compile("public\\s+(static\\s+)?void\\s+main\\s*\\(\\s*String\\s*[^),]*\\)");
				Matcher matcher = pattern.matcher(text);
				return matcher.find();
			} catch (Exception e) {
				e.printStackTrace();
			}
			//in case of an error better return true
			return true;
		}
		
		   /**
	     * Returns a string containing the contents of the given file.
	     * 
	     * @throws CoreException 
	     * @throws IOException 
	     */
	    private String getString(IFile file) throws CoreException, IOException {
	        InputStream contentStream = file.getContents();
	        Reader in = new InputStreamReader(contentStream);

	        int chunkSize = contentStream.available();
	        StringBuffer buffer = new StringBuffer(chunkSize);
	        char[] readBuffer = new char[chunkSize];
	        
	        int n = in.read(readBuffer);
	        while (n > 0) {
	            buffer.append(readBuffer);
	            n = in.read(readBuffer);
	        }

	        contentStream.close();
	        return buffer.toString();
	    }
	}
	
}
