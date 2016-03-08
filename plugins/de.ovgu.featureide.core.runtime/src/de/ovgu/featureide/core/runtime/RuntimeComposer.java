package de.ovgu.featureide.core.runtime;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.FileSystems;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResourceDelta;

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
 * Authors: Kai Wolf, Matthias Quaas
 *
 */
public class RuntimeComposer extends ComposerExtensionClass {

	@Override
	public Mechanism getGenerationMechanism() {
		return null;
	}

	@Override
	public void performFullBuild(IFile config) {
		String dirProj = featureProject.getProject().getLocationURI().getPath().toString();
		File fileProp = new File(dirProj + FileSystems.getDefault().getSeparator() + "runtimeProps.properties");

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
}
