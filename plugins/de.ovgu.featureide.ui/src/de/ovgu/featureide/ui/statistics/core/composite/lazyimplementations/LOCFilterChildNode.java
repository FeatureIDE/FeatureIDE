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

import java.util.HashMap;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.core.IFeatureProject;
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
		super(description, fileFeatureLOCMapper, project);
		this.parentNodeName = parentNodeName;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.LOCFilterNode#initChildren()
	 */
	@Override
	protected void initChildren() {
		if (parentNodeName.equals(LOC_BY_EXTENSION)) {
			String extension = description.split(SEPARATOR)[0];
			HashMap<IFile, Integer> filesWithLOC = fileFeatureLOCMapper.getFilesWithLOCByExtension(extension);

			for (IFile file: filesWithLOC.keySet()) {
				String sourceFolder = fileFeatureLOCMapper.getSourceFolder().getName() + "/";
				String filePath = file.getFullPath().toString();
				
				String[] path = filePath.split(sourceFolder);
				String prettyPath = path[0];
				if (path.length > 1) {
					prettyPath = path[1];
				}
				addChild(new DirectivesLeafNode(prettyPath, filesWithLOC.get(file), project, prettyPath));
			}
		}
	}

}
