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

import de.ovgu.featureide.fm.core.Feature;

import AST.CompilationUnit;

/**
 * TODO description
 * 
 * @author soenke
 */
public class FeatureEntry {
	private List<CUTableEntry> compilation_units = new ArrayList<CUTableEntry>();
	private Feature feature;
	private String feature_path;

	public FeatureEntry(Feature feature, String feature_path) {
		this.feature = feature;
		this.feature_path = feature_path;
	}
	
	public boolean providesType(String type){
		for(CUTableEntry entry : compilation_units){
			if(entry.providesType(type)){
				return true;
			}
		}
		return false;
	}
	
	public boolean providesMethod(String type, String signature){
		for(CUTableEntry entry : compilation_units){
			if(entry.providesMethod(type, signature)){
				return true;
			}
		}
		return false;
	}
	
	public void addCU(CompilationUnit cu) {
		compilation_units.add(new CUTableEntry(cu, feature_path, feature));
	}
	
	public Feature getFeature(){
		return feature;
	}
}
