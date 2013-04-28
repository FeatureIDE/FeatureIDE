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
package de.ovgu.featureide.fm.core.constraint;

/**
 * Reference to a feature.
 * 
 * @author Sebastian Henneberg
 */
public class Reference {

	private String featureName;
	
	private ReferenceType type;
	
	private String attributeName = null;

	public Reference(String featureName, ReferenceType type, String attributeName) {
		this.featureName = featureName;
		this.type = type;
		this.attributeName = attributeName;
	}
	
	public Reference(String featureName) {
		this.featureName = featureName;
		this.type = ReferenceType.FEATURE;
	}

	public String getFeatureName() {
		return featureName;
	}

	public ReferenceType getType() {
		return type;
	}

	public String getAttributeName() {
		return attributeName;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(featureName);
		
		switch (type) {
		case ATTRIBUTE:
			sb.append(".");
			sb.append(attributeName);
			break;
		case ATTRIBUTE_SUM:
			sb.append("#.");
			sb.append(attributeName);
			break;
		case FEATURE:
			break;
		default:
			break;
		}
		
		return sb.toString();
	}
}
