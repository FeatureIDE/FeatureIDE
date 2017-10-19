/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.visualization;

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;

/**
 * Configurations Analysis utils
 *
 * @author Jabier Martinez
 */
public class ConfigAnalysisUtils {

	/**
	 * Get a matrix configurations/features
	 *
	 * @param featureProject
	 * @param featureList
	 * @return boolean[][]
	 * @throws CoreException
	 */
	public static boolean[][] getConfigsMatrix(IFeatureProject featureProject, List<String> featureList) throws CoreException {
		final Collection<Configuration> configs = new ArrayList<>();
		// check that they are config files
		final IFolder configsFolder = featureProject.getConfigFolder();
		for (final IResource res : configsFolder.members()) {
			if ((res instanceof IFile) && res.isAccessible()) {
				final Configuration configuration = new Configuration(featureProject.getFeatureModel());
				final ProblemList problems = SimpleFileHandler.load(Paths.get(res.getLocationURI()), configuration, ConfigFormatManager.getInstance());
				if (!problems.containsError()) {
					configs.add(configuration);
				}
			}
		}

		final boolean[][] matrix = new boolean[configs.size()][featureList.size()];
		int iconf = 0;
		for (final Configuration configuration : configs) {
			final Set<String> configFeatures = configuration.getSelectedFeatureNames();
			int ifeat = 0;
			for (final String f : featureList) {
				matrix[iconf][ifeat] = configFeatures.contains(f);
				ifeat++;
			}
			iconf++;
		}

		return matrix;
	}

	/**
	 * No core nor hidden features
	 *
	 * @param featureProject
	 * @return list of feature names
	 */
	public static List<String> getNoCoreNoHiddenFeatures(IFeatureProject featureProject) {
		// make a copy because it is unmodifiable
		final List<String> featureList1 = featureProject.getFeatureModel().getFeatureOrderList();
		final List<String> featureList = new ArrayList<String>();
		featureList.addAll(featureList1);
		final List<IFeature> coreFeatures = featureProject.getFeatureModel().getAnalyser().getCoreFeatures();
		final Collection<IFeature> hiddenFeatures = featureProject.getFeatureModel().getAnalyser().getHiddenFeatures();
		for (final IFeature coref : coreFeatures) {
			featureList.remove(coref.getName());
		}
		for (final IFeature hiddenf : hiddenFeatures) {
			featureList.remove(hiddenf.getName());
		}
		return featureList;
	}
}
