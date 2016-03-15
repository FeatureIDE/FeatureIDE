package de.ovgu.featureide.core.runtime;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
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

	private final static String COMPOSER_ID = "de.ovgu.featureide.core.composer.runtime";

	public void launch(ILaunchConfiguration configuration, String mode, ILaunch launch, IProgressMonitor monitor)
			throws CoreException {
		ILaunchConfigurationWorkingCopy launchConfigCopy = configuration.getWorkingCopy();
		IFeatureProject featureProject = null;

		if (launchConfigCopy.getMappedResources().length == 1) {
			featureProject = CorePlugin.getFeatureProject(launchConfigCopy.getMappedResources()[0]);
		}

		if (featureProject != null && featureProject.getComposerID().equals(COMPOSER_ID)
				&& RuntimeComposer.COMPOSITION_MECHANISMS[0].equals(featureProject.getCompositionMechanism())) {

			final Configuration featureProjectConfig = new Configuration(featureProject.getFeatureModel());

			String userDefinedArgs = launchConfigCopy
					.getAttribute(IJavaLaunchConfigurationConstants.ATTR_PROGRAM_ARGUMENTS, "");

			String configPath = featureProject.getCurrentConfiguration().getRawLocation().toOSString();
			FileReader<Configuration> reader = new FileReader<>(configPath, featureProjectConfig,
					ConfigurationManager.getFormat(configPath));
			reader.read();

			String args = userDefinedArgs;
			for (SelectableFeature f : featureProjectConfig.getFeatures()) {
				if (!f.getFeature().getStructure().isAbstract()) {
					if (f.getSelection() == Selection.SELECTED) {
						args += " " + f.getFeature().getName();
						launchConfigCopy.setAttribute(IJavaLaunchConfigurationConstants.ATTR_PROGRAM_ARGUMENTS, args);
					}
				}
			}

			new org.eclipse.jdt.launching.JavaLaunchDelegate().launch(launchConfigCopy, mode, launch, monitor);

			launchConfigCopy.setAttribute(IJavaLaunchConfigurationConstants.ATTR_PROGRAM_ARGUMENTS, userDefinedArgs);
			configuration = launchConfigCopy.doSave();

		} else {
			new org.eclipse.jdt.launching.JavaLaunchDelegate().launch(launchConfigCopy, mode, launch, monitor);
		}
	}
}