/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.core.typecheck.parser;

import java.util.ArrayList;
import java.util.List;

import AST.CompilationUnit;

import de.ovgu.featureide.fm.core.Feature;

/**
 * TODO description
 * 
 * @author soenke
 */
public class CUTable {
	private List<FeatureEntry> features = new ArrayList<FeatureEntry>();

	public CUTable() {

	}

	public List<Feature> providesType(String type) {
		List<Feature> providing_features = new ArrayList<Feature>();

		for (FeatureEntry entry : features) {
			if (entry.providesType(type)) {
				providing_features.add(entry.getFeature());
			}
		}

		return providing_features;
	}

	public List<Feature> providesMethod(String type, String signature) {
		List<Feature> providing_features = new ArrayList<Feature>();

		for (FeatureEntry entry : features) {
			if (entry.providesMethod(type, signature)) {
				providing_features.add(entry.getFeature());
			}
		}

		return providing_features;
	}

	public void addCU(Feature feature, String feature_path, CompilationUnit cu) {
		FeatureEntry entry = getCU(feature);
		if (entry == null) {
			entry = new FeatureEntry(feature, feature_path);
			features.add(entry);
		}
		entry.addCU(cu);
	}

	public FeatureEntry getCU(Feature feature) {
		for (FeatureEntry entry : features) {
			if (entry.getFeature().equals(feature)) {
				return entry;
			}
		}
		return null;
	}

	public List<FeatureEntry> getFeatureEntries() {
		return features;
	}
}
