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
package de.ovgu.featureide.fm.core;

/**
 * TODO description
 * 
 * @author Christopher Kruczek
 * @author Andy Kenner
 */
public class HotSpotResult {
	private String featureName;
	private double metricValue;
	
	public void setFeatureName(String featureName) {
		this.featureName = featureName;
	}
	public void setMetricValue(double metricValue) {
		this.metricValue = metricValue;
	}
	public String getFeatureName() {
		return featureName;
	}
	public double getMetricValue() {
		return metricValue;
	}
	
	@Override
	public boolean equals(Object arg0) {
		if(arg0 == null)
			return false;
		if(!(arg0 instanceof HotSpotResult))
			return false;
					
		HotSpotResult result = (HotSpotResult)arg0;
		return result.getFeatureName().equals(this.featureName);
	}
	
}
