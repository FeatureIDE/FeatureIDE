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
package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import static de.ovgu.featureide.fm.core.localization.StringTable.LOC_BY_EXTENSION;
import static de.ovgu.featureide.fm.core.localization.StringTable.LOC_BY_FEATURE;
import static de.ovgu.featureide.fm.core.localization.StringTable.VARIABLE_LOC;
import static de.ovgu.featureide.fm.core.localization.StringTable.NON_VARIABLE_LOC;
import static de.ovgu.featureide.fm.core.localization.StringTable.PP_LOC;

import java.util.HashMap;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.datatypes.FileFeatureLOCMapper;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes.AbstractSortModeNode;

/**
 * Adds the second layer after Lines of Code in statistics.
 * Replaces the old HashMapNodeTwoStrings class.
 * @author Maximilian Homann
 * @author Philipp Kuhn
 */
public class LOCFilterNode extends AbstractSortModeNode {
	protected final FileFeatureLOCMapper fileFeatureLOCMapper;
	protected final String nodeType;
	protected final IFeatureProject project;

	/**
	 * Creates a new LOCFilterNode.<br>
	 * @param description
	 * @param fileFeatureLOCMapper
	 */
	public LOCFilterNode(String description, FileFeatureLOCMapper fileFeatureLOCMapper, IFeatureProject project, String type) {
		super(description);
		this.nodeType = type;
		this.fileFeatureLOCMapper = fileFeatureLOCMapper;
		this.project = project;
	}
	
	/**
	 * Creates a new LOCFilterNode.<br>
	 * @param description
	 * @param loc
	 * @param nodeType
	 * @param fileFeatureLOCMapper
	 */
	public LOCFilterNode(String description, int loc, String nodeType, FileFeatureLOCMapper fileFeatureLOCMapper, IFeatureProject project, String type) {
		super(description, loc);
		this.nodeType = type;
		this.fileFeatureLOCMapper = fileFeatureLOCMapper;
		this.project = project;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.statistics.core.composite.LazyParent#initChildren()
	 */
	@Override
	protected void initChildren() {
		if (nodeType.equals(LOC_BY_EXTENSION)) { 
			HashMap<String, Integer> extAndCount = fileFeatureLOCMapper.getExtensionsWithLOC();
			addExtensionChild(extAndCount);
		} else if (nodeType.equals(LOC_BY_FEATURE)) {
			HashMap<FSTFeature, Integer> featAndCount = fileFeatureLOCMapper.getFeaturesWithLOC();
			for (FSTFeature feature: featAndCount.keySet()) {
				int LOC = featAndCount.get(feature).intValue(); 
				addChild(new Parent(feature.getName(), LOC));
			}		
		} else if (nodeType.equals(NON_VARIABLE_LOC)) {
			HashMap<String, Integer> extAndCount = fileFeatureLOCMapper.getNonVariableLOCByExtension();
			addExtensionChild(extAndCount);
		} else if (nodeType.equals(VARIABLE_LOC)) {
			HashMap<String, Integer> extAndCount = fileFeatureLOCMapper.getVariableLOCByExtension();
			addExtensionChild(extAndCount);			
		} else if(nodeType.equals(PP_LOC)) {
			HashMap<String, Integer> extAndCount = fileFeatureLOCMapper.getPPStatementLOCByExtension();
			addExtensionChild(extAndCount);
		}
	}
	
	/**
	 * Adds a child for each extension found
	 * @param extAndCount A Hashmap which has the loc for each extension saved.
	 */
	public void addExtensionChild(HashMap<String, Integer> extAndCount) {
		for (String extension: extAndCount.keySet()) {
			if (extension != null) {
				int LOC = extAndCount.get(extension).intValue();
				addChild(new LOCFilterChildNode(extension + SEPARATOR + LOC, nodeType, fileFeatureLOCMapper, project));
			}
		}
	}

}
