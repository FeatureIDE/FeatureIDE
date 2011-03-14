/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.featurecpp;

import java.util.ArrayList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.featurecpp.wrapper.FeatureCppWrapper;

/**
 * A FeatureIDE extension to compose FeatureC++ files.
 * 
 * @author Tom Brosch
 * @author Jens Meinicke
 */
public class FeatureCppComposer extends ComposerExtensionClass {

	public static final String COMPOSER_ID = "de.ovgu.featureide.composer.featurecpp";

	private final FeatureCppWrapper featureCpp = new FeatureCppWrapper(
			(FeatureCppCorePlugin.getDefault().getBundle().getLocation() + "lib/fc++v0.8.exe")
			.substring(16));

	public void initialize(IFeatureProject project) {
		if (project == null) {
			return;
		}
		featureCpp.initialize(project.getSourceFolder(), project
				.getBuildFolder());
	}


	public void performFullBuild(IFile config) {
		featureCpp.compose(config);
	}

	@Override
	public ArrayList<String> extensions() {
		ArrayList<String> extensions = new ArrayList<String>();
		extensions.add(".h");
		return extensions;
	}

	@Override
	public ArrayList<String[]> getTemplates(){
		
		ArrayList<String[]> list = new ArrayList<String[]>();
		String[] c = {"C++", "h", ""};
		list.add(c);
		return list;
	}

	@Override
	public void postCompile(IResourceDelta delta, IFile file) {
		try {
			file.refreshLocal(IResource.DEPTH_ZERO, null);
		} catch (CoreException e) {
			FeatureCppCorePlugin.getDefault().logError(e);
		}
	}

	@Override
	public String getConfigurationExtension() {
		return ".equation";
	}
}
