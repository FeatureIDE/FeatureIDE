/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.ui.actions.generator;

import java.io.File;
import java.lang.annotation.Annotation;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;
import java.security.Permission;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.TransformerException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.content.IContentDescription;
import org.eclipse.core.runtime.content.IContentType;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.core.JavaProject;
import org.eclipse.ui.IEditorDescriptor;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.progress.UIJob;
import org.junit.runner.Description;
import org.junit.runner.JUnitCore;
import org.junit.runner.notification.Failure;
import org.junit.runner.notification.RunListener;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.actions.generator.IConfigurationBuilderBasics.BuildType;

/**
 * Runs test cases of the generated product.
 * 
 * @author Jens Meinicke
 */
@SuppressWarnings("restriction")
public class TestRunner {

	private static final Object KEY = new Object();
	private final TestResults testResults;
	private static final UIPlugin LOGGER = UIPlugin.getDefault();
	int compiled = 0;

	private final IFolder tmp;
	private final ConfigurationBuilder builder;

	public TestRunner(IFolder tmp, TestResults testResults, final ConfigurationBuilder builder) {
		this.tmp = tmp;
		this.testResults = testResults;
		this.builder = builder;

	}


	@SuppressWarnings("resource")
	public void runTests(final BuilderConfiguration configuration) {
		URL[] url = getURLs();
		URLClassLoader classLoader = new URLClassLoader(url, Thread.currentThread().getContextClassLoader());
		for (final String file : getFiles(tmp)) {
			try {
				Class<?> clazz = classLoader.loadClass(file);

				if (isModuleTest(clazz)) {
					synchronized (KEY) {
						if (testResults.modulTests.contains(clazz.getName())) {
							continue;
						} else {
							testResults.modulTests.add(clazz.getName());
						}
					}
				}

				JUnitCore core = new JUnitCore();
				core.addListener(new RunListener() {

					long time = 0;

					@Override
					public void testStarted(Description description) throws Exception {
						if (description.toString().startsWith("initializationError")) {
							return;
						}
						time = System.currentTimeMillis();
					}

					@Override
					public void testFinished(Description description) throws Exception {
						if (time == -1) {
							return;
						}
						time = System.currentTimeMillis() - time;
						testResults.addTest(file, (builder.buildType == BuildType.ALL_CURRENT ? "" : ConfigurationBuilder.FOLDER_NAME + "\\") + configuration.getName(), new Test(description.toString(), time, file));
					}

					@Override
					public void testFailure(Failure failure) throws Exception {
						if (failure.getDescription().toString().startsWith("initializationError") || "No runnable methods".equals(failure.getMessage())) {
							time = -1;
							return;
						}
						time = System.currentTimeMillis() - time;
						testResults.addTest(file, (builder.buildType == BuildType.ALL_CURRENT ? "" : ConfigurationBuilder.FOLDER_NAME + "\\") + configuration.getName(), new Test(failure.getTestHeader(), time, file, failure));
						time = -1;
					}

					@Override
					public void testIgnored(Description description) throws Exception {
						testResults.ignored++;
					}

				});
				SecurityManager originalManager = System.getSecurityManager();
				try {
					System.setSecurityManager(NO_EXIT_MANAGER);
					core.run(clazz);
				} finally {
					System.setSecurityManager(originalManager);
				}
			} catch (ClassNotFoundException e) {
				LOGGER.logError(e);
			}
		}

		IFile iResultsXML = CorePlugin.getFeatureProject(tmp).getProject().getFile("test.xml");
		saveResults(iResultsXML, testResults);

	}

	private URL[] getURLs() {
		ArrayList<URL> urls = new ArrayList<>();
		try {
			URL url = tmp.getLocationURI().toURL();
			url = new URL(url.toString() + "/");
			urls.add(url);
			
			JavaProject proj = new JavaProject(tmp.getProject(), null);
			IJavaElement[] elements = proj.getChildren();
			for (IJavaElement e : elements) {
				String path = e.getPath().toOSString();
				if (path.contains(":")) {
					continue;
				}
				IResource resource = e.getResource();
				if (resource != null && "jar".equals(resource.getFileExtension())) {
					urls.add(resource.getRawLocationURI().toURL());
				}
			}
		} catch (MalformedURLException | JavaModelException e) {
			UIPlugin.getDefault().logError(e);
		}

		return urls.toArray(new URL[urls.size()]);
	}

	/**
	 * Checks whether the class is a module test.
	 */
	private boolean isModuleTest(Class<?> clazz) {
		for (Annotation a : clazz.getAnnotations()) {
			if ("@de.ovgu.featureide.ModuleTest()".equals(a.toString())) {
				// somehow clazz.getAnnotation(ModulTest.class) does not work 
				return true;
			}
		}
		return false;
	}

	private static final NoExitSecurityManager NO_EXIT_MANAGER = new NoExitSecurityManager();

	private static class NoExitSecurityManager extends SecurityManager {
		@Override
		public void checkPermission(Permission perm) {
			// allow anything.
		}

		@Override
		public void checkPermission(Permission perm, Object context) {
			// allow anything.
		}

		@Override
		public void checkExit(int status) {
			super.checkExit(status);
			throw new SystemExitException(status);
		}
	}

	@SuppressWarnings("serial")
	private static class SystemExitException extends RuntimeException {
		public SystemExitException(int status) {
			super("Systen.exit: " + status);
		}
	}

	private List<String> getFiles(IFolder folder) {
		try {
			folder.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			LOGGER.logError(e);
		}
		return getFiles(folder, null);
	}

	private List<String> getFiles(IFolder folder, String prefix) {
		List<String> files = new LinkedList<>();
		try {

			for (IResource child : folder.members()) {
				if (child instanceof IFolder) {
					files.addAll(getFiles((IFolder) child, (prefix != null ? prefix + "." : "") + child.getName()));
				} else if (child instanceof IFile) {
					if ("class".equals(child.getFileExtension())) {
						files.add((prefix != null ? prefix + "." : "") + child.getName().substring(0, child.getName().lastIndexOf('.')));
					}
				}
			}
		} catch (CoreException e) {
			LOGGER.logError(e);
		}
		return files;
	}

	private static synchronized void saveResults(IFile iResultsXML, TestResults testResults) {
		File resultsXML = new File(iResultsXML.getLocationURI());
		try {
			new TestXMLWriter(testResults).writeToFile(resultsXML);
			iResultsXML.refreshLocal(IResource.DEPTH_INFINITE, null);
			openJunitView(iResultsXML);
		} catch (ParserConfigurationException | TransformerException | CoreException e) {
			LOGGER.logError(e);
		}
	}

	/**
	 * Tries to open the given xml file on the JUnit view.
	 * 
	 * @param file The xml file to open.
	 */
	private static void openJunitView(final IFile file) {
		if (!file.getFileExtension().equals("xml")) {
			throw new RuntimeException(file + " is no xml file");
		}
		final UIJob job = new UIJob("open " + file) {

			@Override
			public IStatus runInUIThread(IProgressMonitor monitor) {
				IWorkbenchWindow window = UIPlugin.getDefault().getWorkbench().getWorkbenchWindows()[0];
				IWorkbenchPage page = window.getActivePage();
				if (page == null)
					return Status.OK_STATUS;

				try {
					IEditorDescriptor desc = getDescriptor(file);
					if (desc != null) {
						page.openEditor(new FileEditorInput(file), desc.getId());
					}
				} catch (CoreException e) {
					LOGGER.logError(e);
				}
				return Status.OK_STATUS;
			}
		};
		job.schedule();
		try {
			job.join();
		} catch (InterruptedException e) {
			LOGGER.logError(e);
		}
	}

	private static IEditorDescriptor getDescriptor(IFile file) throws CoreException {
		IContentType contentType = null;
		IContentDescription description = file.getContentDescription();
		if (description != null) {
			contentType = description.getContentType();
		}
		if (contentType != null) {
			return PlatformUI.getWorkbench().getEditorRegistry().getDefaultEditor(file.getName(), contentType);
		} else {
			return PlatformUI.getWorkbench().getEditorRegistry().getDefaultEditor(file.getName());
		}
	}
}
