package de.ovgu.featureide.fm.attributes.composer;

import java.nio.file.Paths;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.fm.attributes.format.XmlExtendedFeatureModelFormat;
import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.DefaultFormat;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;

public class ExtendedFeatureModeling extends ComposerExtensionClass {

	@Override
	public void performFullBuild(IFile config) {

	}

	@Override
	public void addCompiler(IProject project, String sourcePath, String configPath, String buildPath) {

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
	public boolean hasBuildFolder() {
		return false;
	}

	@Override
	public boolean hasSource() {
		return false;
	}

	@Override
	public boolean clean() {
		return false;
	}

	@Override
	public void copyNotComposedFiles(Configuration config, IFolder destination) {

	}

	@Override
	public Mechanism getGenerationMechanism() {
		return null;
	}

	@Override
	public void buildConfiguration(IFolder folder, Configuration configuration, String congurationName) {
		try {
			final IContainer parent = folder.getParent();
			if (!parent.exists()) {
				folder.create(true, true, null);
			}
			final IPersistentFormat<Configuration> format = ConfigFormatManager.getInstance().getFormatById(DefaultFormat.ID);
			final IFile configurationFile = parent.getFile(new Path(congurationName + "." + format.getSuffix()));
			SimpleFileHandler.save(Paths.get(configurationFile.getLocationURI()), configuration, format);
			copyNotComposedFiles(configuration, folder);
		} catch (CoreException | NoSuchExtensionException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	@Override
	public boolean supportsMigration() {
		return false;
	}

	@Override
	public boolean createFolderForFeatures() {
		return false;
	}

	@Override
	public void postCompile(IResourceDelta delta, IFile buildFile) {

	}

	@Override
	public boolean showContextFieldsAndMethods() {
		return false;
	}

	@Override
	public IFeatureModelFormat getFeatureModelFormat() {
		return new XmlExtendedFeatureModelFormat();
	}
}
