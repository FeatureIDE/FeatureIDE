package de.ovgu.featureide.core.runtime;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.core.model.ILaunchConfigurationDelegate;
import org.eclipse.jdt.launching.IJavaLaunchConfigurationConstants;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.FileReader;

public class RuntimeLaunchConfigurationDelegate implements ILaunchConfigurationDelegate {

	private final static String id="de.ovgu.featureide.core.composer.runtime";
	
	public void launch(ILaunchConfiguration configuration, String mode, ILaunch launch, IProgressMonitor monitor)
			throws CoreException {
		
		

		ILaunchConfigurationWorkingCopy configCopy = configuration.getWorkingCopy();
		IFeatureProject featureProject = null;

		if (configCopy.getMappedResources().length == 1) {
			featureProject = CorePlugin.getFeatureProject(configCopy.getMappedResources()[0]);
			
		}

		if (featureProject != null && featureProject.getComposerID().equals(id)
				&& RuntimeComposer.COMPOSITION_MECHANISMS[0].equals(featureProject.getCompositionMechanism())) {
			System.out.println("Comp: " + featureProject.getCompositionMechanism());
			
			final Configuration c = new Configuration(featureProject.getFeatureModel());

			String userDefinedArgs = configCopy.getAttribute(IJavaLaunchConfigurationConstants.ATTR_PROGRAM_ARGUMENTS,
					"");

			String configPath = featureProject.getCurrentConfiguration().getRawLocation().toOSString();
			FileReader<Configuration> reader = new FileReader<>(configPath, c,
					ConfigurationManager.getFormat(configPath));
			reader.read();
			String args = userDefinedArgs;

			for (SelectableFeature f : c.getFeatures()) {
				if (!f.getFeature().getStructure().isAbstract()) {
					if (f.getSelection() == Selection.SELECTED) {
						args += " " + f.getFeature().getName();
						configCopy.setAttribute(IJavaLaunchConfigurationConstants.ATTR_PROGRAM_ARGUMENTS, args);
					}

				}
			}

			new org.eclipse.jdt.launching.JavaLaunchDelegate().launch(configCopy, mode, launch, monitor);

			configCopy.setAttribute(IJavaLaunchConfigurationConstants.ATTR_PROGRAM_ARGUMENTS, userDefinedArgs);

			configuration = configCopy.doSave();

		} else {
			new org.eclipse.jdt.launching.JavaLaunchDelegate().launch(configCopy, mode, launch, monitor);

		}
	}

}
