package de.ovgu.featureide.core.runtime;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Properties;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.DefaultFormat;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.FileReader;

/**
 * Images composer through images overlapping. Images in the different feature
 * folders need to have the same relative path to be combined.
 * 
 * @author Jabier Martinez
 *
 */
public class RuntimeComposer extends ComposerExtensionClass {

	@Override
	public Mechanism getGenerationMechanism() {
		return null;
	}

	@Override
	public void performFullBuild(IFile config) {

		final String strFalse = "false";
		final String strTrue = "true";

		
	    String dirProj = featureProject.getProject().getLocationURI().getPath().toString();
		File fileProp = new File(dirProj + "\\beispiel.properties");

		String configPath = config.getRawLocation().toOSString();

		final Configuration configuration = new Configuration(featureProject.getFeatureModel());
		FileReader<Configuration> reader = new FileReader<>(configPath, configuration,
				ConfigurationManager.getFormat(configPath));
		reader.read();

		try (BufferedWriter writer = new BufferedWriter(new FileWriter(fileProp))) {

			for (SelectableFeature f : configuration.getFeatures()) {

				if (!f.getFeature().getStructure().isAbstract())
					writer.write(f.getFeature().getName() + "="
							+ (f.getSelection().name() == Selection.SELECTED.name() ? strTrue : strFalse) + "\n");

			}
			writer.close();

		} catch (IOException e) {
			e.printStackTrace();
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
		try {
			buildFile.setDerived(false, null);
		} catch (CoreException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	/**
	 * Order the features in case of user-defined ordering
	 * 
	 * @param selectedFeatures
	 * @return ordered features
	 */
	private List<IFolder> orderSelectedFeatures(List<IFolder> selectedFeatures) {
		// Order them if needed
		Collection<String> featureOrderList = featureProject.getFeatureModel().getFeatureOrderList();
		if (featureOrderList != null && !featureOrderList.isEmpty()) {
			List<IFolder> orderedFeatures = new ArrayList<IFolder>();
			for (String feature : featureOrderList) {
				IFolder folder = featureProject.getSourceFolder().getFolder(feature);
				if (selectedFeatures.contains(folder)) {
					orderedFeatures.add(folder);
				}
			}
			return orderedFeatures;
		}
		return selectedFeatures;
	}

	/**
	 * Get selected features
	 * 
	 * @param config
	 * @return list of IFolders of the features
	 * @throws FileNotFoundException
	 * @throws IOException
	 */
	private List<IFolder> getSelectedFeatures(IFile config) throws FileNotFoundException, IOException {
		List<IFolder> selectedFeatures = new ArrayList<IFolder>();
		BufferedReader reader = null;
		if (config != null) {
			try {
				reader = new BufferedReader(new InputStreamReader(new FileInputStream(config.getRawLocation().toFile()),
						Charset.availableCharsets().get("UTF-8")));
				String line = null;
				while ((line = reader.readLine()) != null) {
					if (line.startsWith("#"))
						continue;
					IFolder f = featureProject.getSourceFolder().getFolder(line);
					if (f != null) {
						if (!selectedFeatures.contains(f)) {
							selectedFeatures.add(f);
						}
					}
				}
			} finally {
				if (reader != null) {
					reader.close();
				}
			}
		}
		return selectedFeatures;
	}

	/**
	 * Get all files recursively
	 * 
	 * @param dir
	 * @return files
	 */
	public static List<File> getAllFiles(File dir) {
		return getAllFiles(null, dir);
	}

	/**
	 * getAllFiles recursively, initialize files with null
	 * 
	 * @param files
	 * @param dir
	 * @return
	 */
	private static List<File> getAllFiles(List<File> files, File dir) {
		if (files == null) {
			files = new ArrayList<File>();
		}

		if (!dir.isDirectory()) {
			files.add(dir);
			return files;
		}

		for (File file : dir.listFiles()) {
			getAllFiles(files, file);
		}
		return files;
	}

	@Override
	public boolean clean() {
		return false;
	}
}
