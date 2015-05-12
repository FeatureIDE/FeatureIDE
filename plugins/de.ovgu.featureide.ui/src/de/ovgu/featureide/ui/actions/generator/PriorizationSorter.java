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

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

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
	HashMap<String,Double> configsDistancesResult = new HashMap<String,Double>();

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
	
		// bring the first product with maximum number of optional feature.\
		allconfigs.addAll(configs);
		
		configsDistancesResult=getconfigsDistanceMap(allconfigs);
		allyesconfig();
		monitor.worked(1);
			while (!allconfigs.isEmpty()) {
			selectConfig();
			monitor.worked(1);
		}
		
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

	
	private HashMap<String,Double> getconfigsDistanceMap(List<List<String>> allConfig)
	{
		configsDistancesResult = new HashMap<String,Double>();
		String mapKey ;
		for(int i =0; i< allConfig.size() ; i++)
		{

			for (int j = i+1 ; j < allConfig.size() ; j++ )
			{

				int xHashCode = allConfig.get(i).hashCode();
				int yHashCode = allConfig.get(j).hashCode();
				
				mapKey = xHashCode + "_" + yHashCode;

				if(configsDistancesResult.get(mapKey) == null) // not added before
				{
					configsDistancesResult.put(mapKey, clacDistance(allConfig.get(i),allConfig.get(j)));
				}

			}


		}

	
		return configsDistancesResult;
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
		
		int xHashCode = 0;
		int yHashCode = 0;
		
		String mapKeyXY;
		String mapKeyYX;
		
		for (List<String> x : allconfigs) {

			double tempDistance = 0.0;
			for (List<String> y : allsortedconfigs) {
				xHashCode = x.hashCode();
				yHashCode = y.hashCode();
				
				mapKeyXY = xHashCode + "_" + yHashCode;
				mapKeyYX = yHashCode + "_" + xHashCode;
				double tempDistanceLocal = 0.0;
				if(configsDistancesResult.get(mapKeyXY) != null)
				{
					tempDistanceLocal = configsDistancesResult.get(mapKeyXY);
				}else if (configsDistancesResult.get(mapKeyYX) != null)
				{
					tempDistanceLocal = configsDistancesResult.get(mapKeyYX);
					
				}
				else
				{
					System.out.println("we shouldn't get here,  here is wrong");
				}
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
//		
		Collection<String> similar = new HashSet<String>(x);
		Collection<String> different = new HashSet<String>();
		
		different.addAll(x);
		different.addAll(y);
		similar.retainAll(y);
		
		different.removeAll(similar);
		
		double s=similar.size();
		double d=different.size();
		double t=concreteFeatures.size();
		
		//return (similar.size() + (concreteFeatures.size() - (similar.size() + different.size()))) / (double)concreteFeatures.size();
		return (s+(t-(s+d)))/t;
	}

}
