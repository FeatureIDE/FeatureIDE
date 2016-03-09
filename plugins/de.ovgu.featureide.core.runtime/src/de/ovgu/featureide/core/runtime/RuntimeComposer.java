package de.ovgu.featureide.core.runtime;

import static de.ovgu.featureide.fm.core.localization.StringTable.RESTRICTION;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.net.URL;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.LinkOption;
import java.nio.file.StandardCopyOption;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Path;
import org.eclipse.ui.internal.util.BundleUtility;

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
@SuppressWarnings(RESTRICTION)
public class RuntimeComposer extends ComposerExtensionClass {

	@Override
	public void performFullBuild(IFile config) {
		String dirProj = featureProject.getProject().getLocationURI().getPath().toString();
		File fileProp = new File(dirProj + FileSystems.getDefault().getSeparator() + "runtime.properties");

		String configPath = config.getRawLocation().toOSString();

		final Configuration configuration = new Configuration(featureProject.getFeatureModel());
		FileReader<Configuration> reader = new FileReader<>(configPath, configuration,
				ConfigurationManager.getFormat(configPath));
		reader.read();

		try (PrintWriter writer = new PrintWriter(new FileWriter(fileProp))) {
			for (SelectableFeature f : configuration.getFeatures()) {
				if (!f.getFeature().getStructure().isAbstract()) {
					writer.println(f.getFeature().getName() + '=' + (f.getSelection() == Selection.SELECTED
							? Boolean.TRUE.toString() : Boolean.FALSE.toString()));
				}
			}
		} catch (IOException e) {
			RuntimeCorePlugin.getDefault().logError(e);
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

	@Override
	public boolean initialize(IFeatureProject project) {

		if (super.initialize(project)) {
			URL url = BundleUtility.find(RuntimeCorePlugin.getDefault().getBundle(), "Resources/PropertyManager.txt");
			try {
				url = FileLocator.toFileURL(url);
			} catch (IOException e) {
				RuntimeCorePlugin.getDefault().logError(e);
			}

			File fileSource = new File(url.getFile());
			File fileDest = new File(project.getBuildPath().toString() + FileSystems.getDefault().getSeparator()
					+ "PropertyManager.java");

			if (Files.notExists(fileDest.toPath(), LinkOption.NOFOLLOW_LINKS)) {

				try {
					Files.copy(fileSource.toPath(), fileDest.toPath(), StandardCopyOption.REPLACE_EXISTING);
				} catch (IOException e) {
					RuntimeCorePlugin.getDefault().logError(e);
				}
			}
		}
		return super.initialize(project);
	}

	@Override
	public Mechanism getGenerationMechanism() {
		return null;
	}

}
