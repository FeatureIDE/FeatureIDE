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
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;
import java.security.Permission;
import java.util.LinkedList;
import java.util.List;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.TransformerException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.junit.runner.Description;
import org.junit.runner.JUnitCore;
import org.junit.runner.notification.Failure;
import org.junit.runner.notification.RunListener;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * Runs test cases of the generated product.
 * 
 * @author Jens Meinicke
 */
public class TestRunner {

	final TestResults testResults;
	private static final UIPlugin LOGGER = UIPlugin.getDefault();
	int compiled = 0;

	private final IFolder tmp;

	public TestRunner(IFolder tmp, TestResults testResults) {
		this.tmp = tmp;
		this.testResults = testResults;

	}

	public void runTests(final BuilderConfiguration configuration) {
		LOGGER.logInfo("run tests for " + configuration);
		for (final String file : getFiles(tmp)) {
			try {
				URL url = tmp.getLocationURI().toURL();
				url = new URL(url.toString() + "/");
				@SuppressWarnings("resource")
				URLClassLoader classLoader = new URLClassLoader(new URL[] { url }, Thread.currentThread().getContextClassLoader());
				Class<?> clazz = classLoader.loadClass(file);

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

					/* (non-Javadoc)
					 * @see org.junit.runner.notification.RunListener#testFinished(org.junit.runner.Description)
					 */
					@Override
					public void testFinished(Description description) throws Exception {
						if (time == -1) {
							return;
						}
						time = System.currentTimeMillis() - time;
						testResults.addTest(file, configuration.getName(), new Test(description.toString(), time, file));
					}

					/* (non-Javadoc)
					 * @see org.junit.runner.notification.RunListener#testFailure(org.junit.runner.notification.Failure)
					 */
					@Override
					public void testFailure(Failure failure) throws Exception {
						if (failure.getDescription().toString().startsWith("initializationError") || "No runnable methods".equals(failure.getMessage())) {
							time = -1;
							return;
						}
						time = System.currentTimeMillis() - time;
						testResults.addTest(file, configuration.getName(), new Test(failure.getTestHeader(), time, file, failure));
						time = -1;
					}

					/* (non-Javadoc)
					 * @see org.junit.runner.notification.RunListener#testIgnored(org.junit.runner.Description)
					 */
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
			} catch (MalformedURLException e) {
				LOGGER.logError(e);
			} catch (ClassNotFoundException e) {
				LOGGER.logError(e);
			}
		}

		IFile iResultsXML = CorePlugin.getFeatureProject(tmp).getProject().getFile("test.xml");
		File resultsXML = new File(iResultsXML.getLocationURI());
		try {
			new TestXMLWriter(testResults).writeToFile(resultsXML);
			iResultsXML.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (ParserConfigurationException | TransformerException | CoreException e) {
			LOGGER.logError(e);
		}
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
			throw new RuntimeException("System.exit " + status);
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
}
