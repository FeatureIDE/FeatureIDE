/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ui.actions.generator;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.Selection;

/**
 * TODO description
 * 
 * @author Mustafa Alhajjaj
 */
public class PriorizationSorter extends AbstractConfigurationSorter {
	private final List<List<String>> allconfigs = new ArrayList<List<String>>();
	private final List<List<String>> allsortedconfigs = new ArrayList<List<String>>();

	//	private static final UIPlugin LOGGER = UIPlugin.getDefault();
	private FeatureModel featureModel;

	public PriorizationSorter(FeatureModel featureModel) {
		super(featureModel);
		this.featureModel = featureModel;
	}
	
	private int configurationCounter = 1;

	@Override
	public int sort(final IProgressMonitor monitor) {
		if (configurations.isEmpty()) {
			return 0;
		}
		final List<List<String>> configs = new LinkedList<List<String>>();
		for (final BuilderConfiguration c : configurations) {
			configs.add(new ArrayList<String>(c.getSelectedFeatureNames()));
		}
		configurations.clear();
		final List<List<String>> sortedConfigs = sortConfigs(configs, monitor);
		for (final List<String> solution : sortedConfigs) {
			System.out.println("Create configs " + configurationCounter + " of " + sortedConfigs.size());
			configurations.add(createConfiguration(solution, configurationCounter++));
		}
		return configurations.size();
	}
	
	private BuilderConfiguration createConfiguration(final List<String> solution, int i) {
		final Configuration configuration = new Configuration(featureModel, false);
		for (final String selection : solution) {
			configuration.setManual(selection, Selection.SELECTED);
		}
		return new BuilderConfiguration(configuration, i);
	}

	protected List<List<String>> sortConfigs(List<List<String>> configs, IProgressMonitor monitor) {
//		LOGGER.logInfo("Start sorting configurations by difference");
//		final long time = System.currentTimeMillis();
		monitor.beginTask("Sort configurations" , configs.size());
		// the main method.
		// bring the first product with maximum number of optional feature.\
//		List<List<String>> configurations_ = new ArrayList<List<String>>();

//		System.out.println(concreteFeatures);
		allconfigs.addAll(configs);
		allyesconfig();
		monitor.worked(1);
		// all the other elements from the original to the new list one by one
		// based on the similarty
//		int list_length = allconfigs.size();

		while (!allconfigs.isEmpty()) {
//			int sorted_list = allsortedconfigs.size();
//			double max_distance = -1.0;
			selectConfig();
			monitor.worked(1);
		}
		// System.out.println("welcome test "+allsortedconfigs);
//		LOGGER.logInfo(System.currentTimeMillis() - time + "ms to sort all configs");
		return allsortedconfigs;
	}
	
	

	@Override
	public synchronized BuilderConfiguration getConfiguration(boolean sort) {
		if (sort) {
			if (allsortedconfigs.isEmpty()) {
				return createConfiguration(allyesconfig(), configurationCounter++);
			} else if (!allconfigs.isEmpty()){
				return createConfiguration(selectConfig(), configurationCounter++);
			} else {
				return null;
			}
		} else {
			return super.getConfiguration(sort);
		}
	}
	
	@Override
	public synchronized void addConfiguration(BuilderConfiguration configuration, boolean sort) {
		if (sort) {
			allconfigs.add(new ArrayList<String>(configuration.getSelectedFeatureNames()));
		} else {
			super.addConfiguration(configuration, sort);
		}
	}
	
	@Override
	public int getBufferSize() {
		return allconfigs.size() + configurations.size();
	}

	private List<String> allyesconfig() {
		// here add the first element to the allsortedconfig list
		// and Remove the element from the original list which is already added
		// to the new sorted list
		int allYes = 0;
		int index = 0;

		for (List<String> x : allconfigs) {
			int tempAllYes = x.size();
			if (tempAllYes > allYes) {
				allYes = tempAllYes;
				index = allconfigs.indexOf(x);
			}
		}

		allsortedconfigs.add(allconfigs.get(index));
		return allconfigs.remove(index);

	}
	
	private List<String> selectConfig() {
		double distance = 1.0;
		int index = 0;
		double tempDistance = 0.0;
		for (List<String> x : allconfigs) {
			for (List<String> y : allsortedconfigs) {
				double tempDistanceLocal = clacDistance(x, y);
				// temp_distance= temp_distance+clac_distance2(x,y);
//				if (tempDistance > tempDistanceLocal) {
//					tempDistance = tempDistanceLocal;
//				}
				if(tempDistanceLocal>tempDistance){
		            tempDistance=tempDistanceLocal;
		        }
			}

			if (tempDistance < distance) {
				distance = tempDistance;
				index = allconfigs.indexOf(x);
			}
		}
//		LOGGER.logInfo("Distance: " + distance);
		allsortedconfigs.add(allconfigs.get(index));
		return allconfigs.remove(index);
	}

	private double clacDistance(List<String> x, List<String> y) {
//		double distance = 0.0;
//		double q = 0.0; // in this variable, i will save the number of features
//						// that exist in both configs ,sortedconfig;
//		double r = 0.0; // i will save the number of features that not exist in
//						// both configs and sortedconfig list
		Collection<String> similar = new HashSet<String>(x);
		Collection<String> different = new HashSet<String>();
		different.addAll(x);
		different.addAll(y);
		similar.retainAll(y);
		different.removeAll(similar);
		return (similar.size() + (concreteFeatures.size() - (similar.size() + different.size()))) / (double)concreteFeatures.size();
	}

}
