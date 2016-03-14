package de.ovgu.featureide.core.framework;

import java.io.BufferedInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.nio.file.FileSystems;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.jar.JarOutputStream;
import java.util.zip.ZipEntry;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.core.framework.activator.FrameworkCorePlugin;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.FileReader;

/**
 * Framework composer updating .classpath file of eclipse
 * 
 * @author Daniel Hohmann
 *
 */
public class FrameworkComposer extends ComposerExtensionClass {

	private LinkedList<String> selectedFeatures;

	@Override
	public Mechanism getGenerationMechanism() {
		return null;
	}

	@Override
	public void copyNotComposedFiles(Configuration c, IFolder destination) {
		/** Should do nothing, otherwise will copy jar files to src folder **/
	}

	/**
	 * Creates JARs from all project in "resources" folder inside the main
	 * projects
	 * 
	 * @return <code>false</code> if creation was not successful
	 */
	private boolean createJARs(IProject project) {
		IFolder resources = project.getFolder("projects");
		IFolder features = featureProject.getSourceFolder();

		try {
			for (IResource res : resources.members()) {
				if (res instanceof IFolder && selectedFeatures.contains(res.getName())) {
					String jarName = res.getName() + ".jar";
					IFile infoFile = ((IFolder) res).getFile("info.xml");
					if (!FrameworkValidator.validate(infoFile)) {
						return false;
					}

					IFolder bin = ((IFolder) res).getFolder("bin");
					final String path = features.getLocation()
							.append(res.getName() + FileSystems.getDefault().getSeparator() + jarName).toString();
					try (FileOutputStream fileStream = new FileOutputStream(path);
							JarOutputStream jarStream = new JarOutputStream(fileStream)) {
						addToJAR(jarStream, bin);
						addFileToJAR(jarStream, infoFile, "");
					} catch (IOException e) {
						FrameworkCorePlugin.getDefault().logError(e);
						return false;
					}
				}
			}
		} catch (CoreException e) {
			FrameworkCorePlugin.getDefault().logError(e);
			return false;
		}
		return true;
	}

	private void addFileToJAR(JarOutputStream jarStream, IFile res, String path) throws IOException {
		jarStream.putNextEntry(
				new ZipEntry(path + res.getName()));
		URL location = FileLocator.toFileURL(res.getLocationURI().toURL());
		File file = new File(location.getPath());
		try (BufferedInputStream in = new BufferedInputStream(new FileInputStream(file))) {
			byte[] buffer = new byte[1024];
			while (true) {
				int count = in.read(buffer);
				if (count == -1) {
					break;
				}
				jarStream.write(buffer, 0, count);
			}
		}
	}

	private void addToJAR(JarOutputStream jarStream, IResource bin) throws CoreException, IOException {
		if (bin instanceof IFolder) {
			for (IResource member : ((IFolder) bin).members()) {
				addToJAR(jarStream, member, "");
			}
		}
	}

	private void addToJAR(JarOutputStream jarStream, IResource res, String path) throws IOException, CoreException {
		if (res instanceof IFolder) {
			String path2 = path + res.getName()
					+ FileSystems.getDefault().getSeparator();
			jarStream.putNextEntry(new ZipEntry(path2));
			for (IResource member : ((IFolder) res).members()) {
				addToJAR(jarStream, member, path2);
			}
		}
		else if (res instanceof IFile) {
			addFileToJAR(jarStream, (IFile) res, path);
		}
	}

	@Override
	public void performFullBuild(IFile config) {

		final String configPath = config.getRawLocation().toOSString();
		Configuration configuration = new Configuration(featureProject.getFeatureModel());

		FileReader<Configuration> reader = new FileReader<>(configPath, configuration,
				ConfigurationManager.getFormat(configPath));
		reader.read();

		selectedFeatures = new LinkedList<String>();
		for (IFeature feature : configuration.getSelectedFeatures()) {
			selectedFeatures.add(feature.getName());
		}

		IProject project = config.getProject();
		try {
			project.deleteMarkers("de.ovgu.featureide.core.featureModuleMarker", true, IResource.DEPTH_ZERO);
		} catch (CoreException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		}
		if (!createJARs(project)) {
			FrameworkCorePlugin.getDefault().logWarning("JARs not build");
			// try {
			// IMarker marker =
			// project.createMarker("de.ovgu.featureide.core.featureModuleMarker");
			// marker.setAttribute(IMarker.MESSAGE, "A problem occured while
			// building JARs");
			// marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
			// } catch (CoreException e) {
			// FrameworkCorePlugin.getDefault().logError(e);
			// }
		}
		;

		setBuildpaths(project);

		try {
			project.refreshLocal(IResource.DEPTH_INFINITE, null);
			featureProject.getProject().build(IncrementalProjectBuilder.FULL_BUILD, null);
		} catch (CoreException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Checks if library jar is inside template folder
	 * 
	 * @param path
	 * @return
	 */
	private boolean isFeatureLib(IPath path) {
		IPath pluginFolder = featureProject.getSourceFolder().getFullPath();
		return pluginFolder.isPrefixOf(path);
	}

	/**
	 * Update .classpath file
	 * 
	 * @param project
	 */
	private void setBuildpaths(IProject project) {

		try {
			IJavaProject javaProject = JavaCore.create(project);
			IClasspathEntry[] oldEntries = javaProject.getRawClasspath();
			List<IClasspathEntry> entries = new ArrayList<IClasspathEntry>();
			/** copy existing non-feature entries **/
			for (int i = 0; i < oldEntries.length; i++) {
				if (oldEntries[i].getEntryKind() == IClasspathEntry.CPE_LIBRARY) {
					IPath path = oldEntries[i].getPath();
					if (!isFeatureLib(path)) {
						entries.add(oldEntries[i]);
					}
				} else {
					entries.add(oldEntries[i]);
				}
			}

			/** add selected features **/
			try {
				for (IResource res : featureProject.getSourceFolder().members()) {
					String featureName = res.getName();
					if (selectedFeatures.contains(featureName)) {
						List<IPath> newEntries = createNewIPath(res);
						for (IPath entry : newEntries) {
							IClasspathEntry newLibraryEntry = JavaCore.newLibraryEntry(entry, null, null);
							entries.add(newLibraryEntry);
						}
					}
				}
			} catch (CoreException e) {
				FrameworkCorePlugin.getDefault().logError(e);
			}

			IClasspathEntry[] result = entries.toArray(new IClasspathEntry[0]);
			javaProject.setRawClasspath(result, null);
		} catch (JavaModelException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * creates a list of jars inside a folder<br>
	 * goes into sub folders
	 * 
	 * @param parentFolder
	 * @return list of jars inside parentFolder
	 */
	private List<IPath> createNewIPath(IResource parentFolder) {
		List<IPath> result = new ArrayList<IPath>();
		try {
			IResource[] members = ((IFolder) parentFolder).members();
			if (members.length <= 0) {
				return Collections.emptyList();
			}
			for (IResource child : members) {
				if (child instanceof IFile) {
					if (child.getFileExtension().equals("jar")) {
						result.add(child.getFullPath());
					}
				} else if (child instanceof IFolder) {
					result.addAll(createNewIPath(child));
				}
			}

		} catch (CoreException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		}
		return result;
	}

	@Override
	public boolean initialize(IFeatureProject project) {
		if (super.initialize(project)) {
			return copyRequiredFiles(project);
		}
		return false;
	}

	boolean isDone = false;

	/**
	 * Copies needed files to project folder<br>
	 * <ul>
	 * <li>Everytime called when a framework project does not contain
	 * pluginLoader or config file</li>
	 * </ul>
	 * 
	 * @param project
	 * 
	 * @return <code>true</code> if files are created without a problem
	 */
	private boolean copyRequiredFiles(IFeatureProject project) {

		/** Copy plugin loader **/
		InputStream inputStream = null;
		try {
			inputStream = FileLocator.openStream(FrameworkCorePlugin.getDefault().getBundle(),
					new Path("resources/PluginLoader.java"), false);
		} catch (IOException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		}

		IFolder folder = project.getProject().getFolder("src");
		IFolder folderLoader = folder.getFolder("loader");
		if (!folderLoader.exists()) {
			try {
				folderLoader.create(true, true, null);
				folderLoader.refreshLocal(IResource.DEPTH_INFINITE, null);
			} catch (CoreException e) {
				FrameworkCorePlugin.getDefault().logError(e);
			}
		}
		IFile file = folderLoader.getFile("PluginLoader.java");
		if (!file.exists()) {
			try {
				file.create(inputStream, true, null);
			} catch (CoreException e) {
				FrameworkCorePlugin.getDefault().logError(e);
			}
		}

		// /** Create config file **/
		// try {
		// inputStream =
		// FileLocator.openStream(FrameworkCorePlugin.getDefault().getBundle(),
		// new Path("resources/config.txt"), false);
		// } catch (IOException e) {
		// e.printStackTrace();
		// }
		// file = folder.getFile("config.txt");
		// if (!file.exists()) {
		// try {
		// file.create(inputStream, true, null);
		// } catch (CoreException e) {
		// FrameworkCorePlugin.getDefault().logError(e);
		// }
		// }
		//
		// try {
		// featureProject.getBuildFolder().refreshLocal(IResource.DEPTH_INFINITE,
		// null);
		// } catch (CoreException e) {
		// FrameworkCorePlugin.getDefault().logError(e);
		// }

		return true;

	}

	@Override
	public boolean clean() {
		return false;
	}

}
