/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ahead.wrapper;

import jak2java.Jak2JavaWrapper;

import java.io.IOException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourceAttributes;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.ahead.AheadCorePlugin;
import de.ovgu.featureide.core.IFeatureProject;


/**
 * The AheadWrapper class encapsulates all functionality that has to do
 * with the ahead tool suite. It provides methods to set the current
 * equation file, to add jak files that should be recompiled due to an
 * inkremental or full build. The build methods are capable of composing
 * jak files to java files as well as reduce jak files to java files and
 * compile java files to class files.
 * 
 * The actual work is than delegated to the dedicated wrapper classes.
 * 
 * @author Tom Brosch
 * @author Thomas Thuem
 */
public class AheadWrapper {

	private Jak2JavaWrapper jak2java;

	private ComposerWrapper composer;

	private JavacWrapper javac;

	public AheadWrapper(IFeatureProject featureProject) {
		jak2java = new Jak2JavaWrapper();
		composer = new ComposerWrapper(featureProject);
		javac = new JavacWrapper(featureProject);
	}

	public void setEquation(IFile equation) throws IOException {
		composer.setEquation(equation);
	}

	public void addJakfile(IFile jakfile) {
		composer.addJakfileToCompose(jakfile);
	}

	public void buildAll() {
		IFile[] jakfiles = null;
		IFile[] javafiles = null;
		
		try {
			jakfiles = composer.composeAll();
		} catch (IOException ex) {
			ex.printStackTrace();
		}
		javafiles = reduceJak2Java(jakfiles);
		compileJavafiles(javafiles);
	}

	public void build() {
		IFile[] jakfiles = null;
		IFile[] javafiles = null;
		jakfiles = composer.compose();
		javafiles = reduceJak2Java(jakfiles);
		compileJavafiles(javafiles);
	}

	private IFile[] reduceJak2Java(IFile[] jakFiles) {
		
		IFile[] javaFiles = new IFile[jakFiles.length];
		String filename = null;
		if (jakFiles != null)
			for (int i = 0; i < jakFiles.length; i++) {
				IFile jakFile = jakFiles[i];
				jak2java.reduce2Java(jakFile.getRawLocation().toFile());

				filename = jakFile.getName();
				filename = filename.substring(0, filename.lastIndexOf('.'));
				javaFiles[i] = ((IFolder)jakFile.getParent()).getFile(filename
						+ ".java");
				
				try {
					javaFiles[i].refreshLocal(IResource.DEPTH_ZERO, null);
					javaFiles[i].setDerived(true);
					ResourceAttributes attr = javaFiles[i].getResourceAttributes();
					if (attr != null) {
						attr.setReadOnly(true);
						javaFiles[i].setResourceAttributes(attr);
					}
				} catch (CoreException e) {
					AheadCorePlugin.getDefault().logError(e);
				}
			}
		return javaFiles;
	}

	private void compileJavafiles(IFile[] javaFiles) {
		if (javaFiles != null && javaFiles.length > 0)
			javac.compile(javaFiles);
	}
	
	public void addBuildErrorListener(AheadBuildErrorListener listener) {
		javac.addBuildErrorListener(listener);
		composer.addBuildErrorListener(listener);
	}

}
