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
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;

/**
 * Configurations Analysis utils
 * 
 * @author jabier.martinez
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
	public static boolean[][] getConfigsMatrix(IFeatureProject featureProject, List<String> featureList)
			throws CoreException {
		Collection<IFile> configs = new ArrayList<IFile>();
		// check that they are config files
		IFolder configsFolder = featureProject.getConfigFolder();
		for (IResource res : configsFolder.members()) {
			if (res instanceof IFile) {
				if (((IFile) res).getName().endsWith(".config")) {
					configs.add((IFile) res);
				}
			}
		}

		boolean[][] matrix = new boolean[configs.size()][featureList.size()];
		int iconf = 0;
		for (IFile config : configs) {
			Configuration configuration = ConfigurationManager.load(Paths.get(config.getLocationURI()));
			configuration.initFeatures(new FeatureModelFormula(featureProject.getFeatureModel()));
			Set<String> configFeatures = configuration.getSelectedFeatureNames();
			int ifeat = 0;
			for (String f : featureList) {
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
		List<String> featureList1 = featureProject.getFeatureModel().getFeatureOrderList();
		List<String> featureList = new ArrayList<String>();
		featureList.addAll(featureList1);
		List<IFeature> coreFeatures = featureProject.getFeatureModelManager().getPersistentFormula().getAnalyzer().getCoreFeatures();
		Collection<IFeature> hiddenFeatures = FeatureUtils.getHiddenFeatures(featureProject.getFeatureModel());
		for (IFeature coref : coreFeatures) {
			featureList.remove(coref.getName());
		}
		for (IFeature hiddenf : hiddenFeatures) {
			featureList.remove(hiddenf.getName());
		}
		return featureList;
	}
}
