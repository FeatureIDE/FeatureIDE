package de.ovgu.featureide.core.runtime;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.FileSystems;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Path;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.core.runtime.activator.RuntimeCorePlugin;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.FileReader;

/**
 * 
 * RuntimeComposer creates .property-file from actual configuration.
 * 
 * @author Matthias Quaas
 * @author Kai Wolf
 *
 */

public class RuntimeComposer extends ComposerExtensionClass {

	static final String[] COMPOSITION_MECHANISMS = new String[] { "Run Configuration","Properties" };

	@Override
	
	
	public String[] getCompositionMechanisms() {

		return COMPOSITION_MECHANISMS;
	}

	/**
	 * Every time the project is built, the config will be read and written into
	 * runtime.properties.
	 */
	@Override
	public void performFullBuild(IFile config) {

		IFile fileProp = featureProject.getProject().getFile("runtime.properties");
		
		if (COMPOSITION_MECHANISMS[1].equals(featureProject.getCompositionMechanism())) {
			
			String configPath = config.getRawLocation().toOSString();

			final Configuration configuration = new Configuration(featureProject.getFeatureModel());
			FileReader<Configuration> reader = new FileReader<>(configPath, configuration,
					ConfigurationManager.getFormat(configPath));
			reader.read();

			String configString = "";

			for (SelectableFeature f : configuration.getFeatures()) {
				if (!f.getFeature().getStructure().isAbstract()) {
					configString += f.getFeature().getName() + '=' + (f.getSelection() == Selection.SELECTED
							? Boolean.TRUE.toString() : Boolean.FALSE.toString()) + "\n";
				}
			}

			configString = configString.substring(0, configString.lastIndexOf('\n'));

			InputStream inputStream = new ByteArrayInputStream(configString.getBytes(StandardCharsets.UTF_8));

			createFile(fileProp, inputStream);

		} else {
			deleteFile(fileProp);
		}

	}

	@Override
	public boolean hasFeatureFolder() {
		return false;
	}

	@Override
	public boolean hasSourceFolder() {
		return false;
	}

	@Override
	public void postCompile(IResourceDelta delta, IFile buildFile) {
	}

	@Override
	public boolean clean() {
		return false;
	}

	private static void deleteFile(IFile file) {

		if (file != null) {
			try {
				file.delete(true, null);
			} catch (CoreException e) {
				RuntimeCorePlugin.getDefault().logError(e);
			}
		}
	}

	private static void createFile(IFile file, InputStream stream) {

		if (file != null) {
			try {
				file.create(stream, true, null);
			} catch (CoreException e) {
				RuntimeCorePlugin.getDefault().logError(e);
			}
		}
	}

	/**
	 * When initialized, the PropertyManager class will be created within the
	 * runtime project, if it does not exists already. The PropertyManager.java
	 * is located in de.ovgu.featureide.core.runtime/resources.
	 */
	@Override
	public boolean initialize(IFeatureProject project) {

		if (super.initialize(project)) {

			final String propertyManager = "PropertyManager.java";
			IFile filePropMan = featureProject.getBuildFolder().getFile(propertyManager);

			if (COMPOSITION_MECHANISMS[1].equals(featureProject.getCompositionMechanism())) {

				InputStream inputStream = null;

				try {
					inputStream = FileLocator.openStream(RuntimeCorePlugin.getDefault().getBundle(),
							new Path("Resources" + FileSystems.getDefault().getSeparator() + propertyManager), false);
				} catch (IOException e) {
					RuntimeCorePlugin.getDefault().logError(e);
				}

				if (!filePropMan.exists()) {

					createFile(filePropMan, inputStream);
					try {
						filePropMan.setDerived(true, null);
					} catch (CoreException e) {
						RuntimeCorePlugin.getDefault().logError(e);
					}

				}

			} else {
				deleteFile(filePropMan);

			}
		}

		return super.initialize(project);
	}

	@Override
	public Mechanism getGenerationMechanism() {
		return null;
	}

}
