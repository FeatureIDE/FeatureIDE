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
package de.ovgu.featureide.core.launching;

import java.io.File;
import java.text.MessageFormat;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jdt.launching.AbstractJavaLaunchConfigurationDelegate;
import org.eclipse.jdt.launching.ExecutionArguments;
import org.eclipse.jdt.launching.IVMRunner;
import org.eclipse.jdt.launching.VMRunnerConfiguration;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.MessageBox;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;


/**
 * This class is part of the launching package. It is invoked by a
 * launching action and performs the launching of an java application.
 * Therefore it sets up the environment in which the application should run.
 * 
 * @author Tom Brosch
 * @author Thomas Thuem
 */
public class LayeredApplicationLaunchConfigurationDelegate extends
	AbstractJavaLaunchConfigurationDelegate  {
	
	public static final String PROJECT_NAME = "PROJECT_NAME";

	public static final String MAIN_CLASS = "MAIN_CLASS";

	@SuppressWarnings("unchecked")
	public void launch(ILaunchConfiguration configuration, String mode,
			ILaunch launch, IProgressMonitor monitor) throws CoreException {

		if (monitor == null) {
			monitor = new NullProgressMonitor();
		}
		
		monitor.beginTask(MessageFormat.format("{0}...", new Object[] {configuration.getName()}), 3); //$NON-NLS-1$
		// check for cancellation
		if (monitor.isCanceled()) {
			return;
		}
		try {
			monitor.subTask("Verifying launch attributes..."); 
			
			String projectName = configuration.getAttribute(PROJECT_NAME, "default project");
			IFeatureProject featureProject = getFeatureProject(projectName);
			if (featureProject == null)
				return;
			
			String packageName = getPackageName(featureProject);
			if (packageName == null)
				return;

			String fullClassName = packageName + "." + configuration.getAttribute(MAIN_CLASS, "default class");
			IVMRunner runner = getVMRunner(configuration, mode);
	
//			File workingDir = verifyWorkingDirectory(configuration);
			File workingDir = featureProject.getBinFolder().getRawLocation().toFile();
			String workingDirName = null;
			if (workingDir != null) {
				workingDirName = workingDir.getAbsolutePath();
			}
			
			// Environment variables
			String[] envp = getEnvironment(configuration);
			
			// Program & VM arguments
			String pgmArgs = getProgramArguments(configuration);
			String vmArgs = getVMArguments(configuration);
			ExecutionArguments execArgs = new ExecutionArguments(vmArgs, pgmArgs);
			
			// VM-specific attributes
			Map vmAttributesMap = getVMSpecificAttributesMap(configuration);
			
			// Classpath
			String[] classpath = getClasspath(configuration);//featureProject.getJavaClassPath();
			
			// Create VM config
			VMRunnerConfiguration runConfig = new VMRunnerConfiguration(fullClassName, classpath);
			runConfig.setProgramArguments(execArgs.getProgramArgumentsArray());
			runConfig.setEnvironment(envp);
			runConfig.setVMArguments(execArgs.getVMArgumentsArray());
			runConfig.setWorkingDirectory(workingDirName);
			runConfig.setVMSpecificAttributesMap(vmAttributesMap);
	
			// Bootpath
			runConfig.setBootClassPath(getBootpath(configuration));
			
			// check for cancellation
			if (monitor.isCanceled()) {
				return;
			}		
			
			// stop in main
			prepareStopInMain(configuration);
			
			// done the verification phase
			monitor.worked(1);

			monitor.subTask("Creating source locator..."); 
			// set the default source locator if required
			setDefaultSourceLocator(launch, configuration);
			monitor.worked(1);		
			
			// Launch the configuration - 1 unit of work
			runner.run(runConfig, launch, monitor);
			
			// check for cancellation
			if (monitor.isCanceled()) {
				return;
			}	
		}
		finally {
			monitor.done();
		}
		
	}
	
	private IFeatureProject getFeatureProject(String projectName) {
		IProject project = ResourcesPlugin.getWorkspace().getRoot().getProject(projectName);
		if (!project.isAccessible()) {
			if (project.exists())
				prompErrorMessage("The project " + projectName + " is not open!");
			else
				prompErrorMessage("No project found with the name " + projectName + "!");
			return null;
		}
		
		IFeatureProject featureProject = CorePlugin.getFeatureProject(project);
		if (featureProject == null)
			prompErrorMessage("The project " + projectName + " is not a FeatureProject!");
		return featureProject;
	}

	private String getPackageName(IFeatureProject featureProject) {
		IFile equationFile = featureProject.getCurrentEquationFile();
		if (equationFile == null) {
			prompErrorMessage("No equation found in project " + featureProject.getProjectName() + "!");
			return null;
		}
		
		String equationFileName = equationFile.getName();
		return equationFileName.substring(0, equationFileName.lastIndexOf("."));
	}

	private void prompErrorMessage(final String message) {
		Display.getDefault().syncExec(new Runnable() {
			public void run() {
				Shell shell = Display.getCurrent().getActiveShell();
				MessageBox box = new MessageBox(shell, SWT.ICON_ERROR);
				box.setText("Error on starting layered application");
				box.setMessage(message);
				box.open();
			}
		});
	}

}
