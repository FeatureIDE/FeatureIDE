/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.base.querying;

import java.util.Arrays;
import java.util.List;
import java.util.NoSuchElementException;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.functional.Functional;

public class QueryEngine implements IEventListener {
	
	protected final IFeatureModel model;
	protected IFeature[] features;
	
	private void buildFeatureIndex() {
		List<IFeature> allFeatures = Functional.toList(model.getFeatures());
		this.features = allFeatures.toArray(new IFeature[allFeatures.size()]);
		Arrays.sort(features, (x,y) -> x.getName().compareTo(y.getName()));
	}

	public QueryEngine(IFeatureModel model) {
		this.model = model;
		model.addListener(this);
		
		buildFeatureIndex();
	}
	
	public IFeature exactMatch(String featureName) {
		final int index = Arrays.binarySearch(features, null, (x,y) -> x.getName().compareTo(featureName));
		if (index < 0)
			throw new NoSuchElementException(featureName);
		else return features[index];
	}

	@Override
	public void propertyChange(FeatureIDEEvent event) {
		buildFeatureIndex();
	}

	public void refreshIndex() {
		buildFeatureIndex();
	}
	
}
