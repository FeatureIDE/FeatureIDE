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

import java.util.HashMap;

import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.datatypes.FileFeatureLOCMapper;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes.AbstractSortModeNode;

/**
 * Replaces the old HashMapNodeTwoStrings class. <br>
 * <p>
 * This class is intended to act as the parent Node for the following
 * categories of LOC statistics:<br>
 * - LOC by extension <br>
 * - LOC by feature <br>
 * - LOC by file <br>
 * </p>
 * @author Maximilian Homann
 * @author Philipp Kuhn
 */
public class LOCFilterNode extends AbstractSortModeNode {

	protected final FileFeatureLOCMapper fileFeatureLOCMapper;
	protected final String nodeType;

	/**
	 * Creates a new LOCFilterNode.<br>
	 * There are currently three possible types for this node: <br>
	 *  - LOC_BY_EXTENSION <br>
	 *  - LOC_BY_FEATURE <br>
	 *  - LOC_BY_FILE <br>
	 * These types exist in the {@link StringTable}
	 * @param description
	 * @param fileFeatureLOCMapper
	 */
	public LOCFilterNode(String description, FileFeatureLOCMapper fileFeatureLOCMapper) {
		super(description);
		this.nodeType = description;
		this.fileFeatureLOCMapper = fileFeatureLOCMapper;
	}
	
	/**
	 * Creates a new LOCFilterNode.<br>
	 * There are currently three possible types for this node: <br>
	 *  - LOC_BY_EXTENSION <br>
	 *  - LOC_BY_FEATURE <br>
	 *  - LOC_BY_FILE <br>
	 * These types exist in the {@link StringTable}
	 * @param description
	 * @param loc
	 * @param nodeType
	 * @param fileFeatureLOCMapper
	 */
	public LOCFilterNode(String description, int loc, String nodeType, FileFeatureLOCMapper fileFeatureLOCMapper) {
		super(description, loc);
		this.nodeType = nodeType;
		this.fileFeatureLOCMapper = fileFeatureLOCMapper;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.statistics.core.composite.LazyParent#initChildren()
	 */
	@Override
	protected void initChildren() {
		if (nodeType.equals(LOC_BY_EXTENSION)) {
			HashMap<String, Integer> extAndCount = fileFeatureLOCMapper.getExtensionsWithLOC(); 
			for (String extension: extAndCount.keySet()) {
				if (extension != null) {
					int LOC = extAndCount.get(extension).intValue();
					addChild(new LOCFilterChildNode(extension + SEPARATOR + LOC, nodeType, fileFeatureLOCMapper));
				}
			}
		} else if (nodeType.equals(LOC_BY_FEATURE)) {
			HashMap<FSTFeature, Integer> featAndCount = fileFeatureLOCMapper.getFeaturesWithLOC();
			if(featAndCount.size()== 0) { 
				addChild(new Parent("No feature LOC count available for this composer."));
			} else {
				for (FSTFeature feature: featAndCount.keySet()) {
					int LOC = featAndCount.get(feature).intValue(); 
					addChild(new Parent(feature.getName(), LOC));
				}
			}
		} 
	}

}
