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
package de.ovgu.featureide.core.search;

import java.util.Collection;

import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.internal.FeatureProject;

/**
 * 
 * @author franziskaheyden
 */
public class FeatureSearch extends Search {

	private IProject[] projects;
	
	public FeatureSearch(String filter, SearchResult result) {
		super(filter, result);
	}

	public FeatureSearch(String filter, IProject[] projects, SearchResult result) {
		super(filter, result);
		this.projects = projects;
	}
	
	@Override
	public boolean performSearch() {
		for(int i = 0; i < projects.length; i++){
			try {
				FeatureProject proj = new FeatureProject(projects[i]);
				FSTModel model = new FSTModel(proj);
				//empty??
				Collection<FSTFeature> features = model.getFeatures();
				for (FSTFeature feature: features){
					//case sensitive, exact comparison
					//features is always empty?!
					if(feature.getName().equals(filter)){
						Result entry = new Result(false,true);
						entry.setFeature(feature);
						result.addResult(entry);
					}
				}
			} catch (Exception e) {
				//TODO catch error
				e.printStackTrace();
				//continue;
			}
		}
		return true;
	}

}
