/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.visualisation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.filter.FeatureSetFilter;
import de.ovgu.featureide.fm.core.filter.HiddenFeatureFilter;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.io.EclipseFileSystem;

/**
 * Configurations Analysis utils
 *
 * @author Jabier Martinez
 */
public class ConfigAnalysisUtils {

	public static boolean[][] getConfigsMatrix(IFeatureProject featureProject, List<String> featureList) throws CoreException {
		final Collection<Configuration> configs = new ArrayList<>();
		// check that they are config files
		final IFolder configsFolder = featureProject.getConfigFolder();
		for (final IResource res : configsFolder.members()) {
			if ((res instanceof IFile) && res.isAccessible()) {
				final Configuration configuration = featureProject.loadConfiguration(EclipseFileSystem.getPath(res));
				if (configuration != null) {
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
	 * @param featureProject feature project
	 * @return list of feature names
	 */
	public static List<String> getNoCoreNoHiddenFeatures(IFeatureProject featureProject) {
		final FeatureModelFormula snapshot = featureProject.getFeatureModelManager().getPersistentFormula();
		final Predicate<IFeature> coreFeatureFilter = new FeatureSetFilter(snapshot.getAnalyzer().getCoreFeatures(null));
		final Predicate<IFeature> hiddenFeatureFilter = new HiddenFeatureFilter();

		final Predicate<IFeature> noCoreNoHiddenFilter = hiddenFeatureFilter.or(coreFeatureFilter).negate();
		return Functional.mapToList(snapshot.getFeatureModel().getFeatures(), noCoreNoHiddenFilter, IFeature::getName);
	}
}
