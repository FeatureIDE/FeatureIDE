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
