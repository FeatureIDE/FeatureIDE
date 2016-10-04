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

import java.util.ArrayList;
import java.util.HashMap;

import org.eclipse.core.resources.IFile;

import static de.ovgu.featureide.fm.core.localization.StringTable.LOC_BY_EXTENSION;
import static de.ovgu.featureide.fm.core.localization.StringTable.LOC_BY_FEATURE;
import static de.ovgu.featureide.fm.core.localization.StringTable.LOC_BY_FILE;

import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.datatypes.FileFeatureLOCMapper;

/**
 * @author Maximilian Homann
 * @author Philipp Kuhn
 */
public class LOCFilterChildNode extends LOCFilterNode {

	private String parentNodeName;
	/**
	 * @param description
	 * @param fileFeatureLOCMapper
	 */
	public LOCFilterChildNode(String description, String parentNodeName, FileFeatureLOCMapper fileFeatureLOCMapper) {
		super(description, fileFeatureLOCMapper);
		this.parentNodeName = parentNodeName;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.LOCFilterNode#initChildren()
	 */
	@Override
	protected void initChildren() {
		if (parentNodeName.equals(LOC_BY_EXTENSION)) {
			String extension = description.split(SEPARATOR)[0];
			HashMap<FSTFeature, Integer> features = fileFeatureLOCMapper.getFeaturesByExtensionWithLOC(extension);

			for (FSTFeature feature: features.keySet()) {
				addChild(new Parent(feature.getName(), features.get(feature)));
			}
		} else if (parentNodeName.equals(LOC_BY_FEATURE)) {
			String feature = description.split(SEPARATOR)[0];
			FSTFeature nodeFeature = fileFeatureLOCMapper.resolveFeature(feature);
			HashMap<String, Integer> extensionsWithLOC = fileFeatureLOCMapper.getExtensionsByFeatureWithLOC(nodeFeature);

			for (String extension: extensionsWithLOC.keySet()) {
				addChild(new Parent(extension, extensionsWithLOC.get(extension)));
			}
		} else if (parentNodeName.equals(LOC_BY_FILE)) {
			String fileName = description.split(SEPARATOR)[0];
			IFile file = fileFeatureLOCMapper.resolveFile(fileName);
			HashMap<FSTFeature, Integer> fileWithLOC = fileFeatureLOCMapper.getLOCByFeatMap(file);
			addChild(new Parent("LOC without features" + SEPARATOR, fileFeatureLOCMapper.locWithoutFeatures(file)));
			for (FSTFeature feature: fileWithLOC.keySet()) {
				addChild(new Parent(feature.getName(), fileWithLOC.get(feature)));
			}
		}
	}

}
