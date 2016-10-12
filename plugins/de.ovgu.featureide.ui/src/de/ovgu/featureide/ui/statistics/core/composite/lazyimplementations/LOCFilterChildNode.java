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
import static de.ovgu.featureide.fm.core.localization.StringTable.VARIABLE_LOC;
import static de.ovgu.featureide.fm.core.localization.StringTable.NON_VARIABLE_LOC;
import static de.ovgu.featureide.fm.core.localization.StringTable.PP_LOC;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
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
	public LOCFilterChildNode(String description, String parentNodeName, FileFeatureLOCMapper fileFeatureLOCMapper, IFeatureProject project) {
		super(description, fileFeatureLOCMapper, project, description);
		this.parentNodeName = parentNodeName;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.LOCFilterNode#initChildren()
	 */
	@Override
	protected void initChildren() {	
		String extension = description.split(SEPARATOR)[0];
		HashMap<IFile, Integer> filesWithLOC = fileFeatureLOCMapper.getFilesWithLOCByExtension(extension);
		String prettyPath = "";
		if (parentNodeName.equals(LOC_BY_EXTENSION)) {		
			for (IFile file: filesWithLOC.keySet()) {
				prettyPath = constructPrettyPath(file);
				addChild(new DirectivesLeafNode(prettyPath, filesWithLOC.get(file), project, prettyPath));
			}
		} else if(parentNodeName.equals(NON_VARIABLE_LOC)) {
			
		} else if(parentNodeName.equals(VARIABLE_LOC)) {	
			for (IFile file: filesWithLOC.keySet()) {
				prettyPath = constructPrettyPath(file);
				int loc = 0;
				HashMap<FSTFeature, Integer> locByFeatMap = fileFeatureLOCMapper.getLOCByFeatMap(file);
				for(Map.Entry<FSTFeature, Integer> entry: locByFeatMap.entrySet()) {
					loc += entry.getValue();
				}
				addChild(new DirectivesLeafNode(prettyPath, loc, project, prettyPath));
			}
		} else if(parentNodeName.equals(PP_LOC)) {
			for (IFile file: filesWithLOC.keySet()) {
				prettyPath = constructPrettyPath(file);
				int loc = fileFeatureLOCMapper.getFeaturesByFile(file).size()*2; //not always working
				addChild(new DirectivesLeafNode(prettyPath, loc, project, prettyPath));
			}
		}
	}
	
	private String constructPrettyPath(IFile file) {
		String sourceFolder = fileFeatureLOCMapper.getSourceFolder().getName() + "/";
		String filePath = file.getFullPath().toString();				
		String[] path = filePath.split(sourceFolder);
		String prettyPath = path[0];
		if (path.length > 1) {
			prettyPath = path[1];
		}
		return prettyPath;
	}

}
