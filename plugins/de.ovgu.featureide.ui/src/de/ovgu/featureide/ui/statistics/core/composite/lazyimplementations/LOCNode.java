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
import static de.ovgu.featureide.fm.core.localization.StringTable.NON_VARIABLE_LOC;
import static de.ovgu.featureide.fm.core.localization.StringTable.VARIABLE_LOC;
import static de.ovgu.featureide.fm.core.localization.StringTable.VARIABLE_LOC_WARNING;
import static de.ovgu.featureide.fm.core.localization.StringTable.PP_LOC;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.datatypes.FileFeatureLOCMapper;

/**
 * Node for aggregated LOC.
 * 
 * @author Schleicher Miro
 * @author Maximilian Homann
 * @author Philipp Kuhn
 */
public class LOCNode extends LazyParent {
	
	private final FileFeatureLOCMapper fileFeatureLOCMapper;
	private boolean isPreprocessor = false;
	private IFeatureProject project;

	LOCNode(String description, IFeatureProject project, boolean isPreprocessor) {
		super(description);
		this.fileFeatureLOCMapper = null;
		this.project = project;
		this.isPreprocessor = isPreprocessor;
	}
	
	public LOCNode(String description, FileFeatureLOCMapper ffLOCMapper, IFeatureProject project, boolean isPreprocessor) {
		super(description);
		this.fileFeatureLOCMapper = ffLOCMapper;
		this.project = project;
		this.isPreprocessor = isPreprocessor;
	}

	@Override
	protected void initChildren() {
		addChild(new LOCFilterNode(LOC_BY_EXTENSION, fileFeatureLOCMapper, project, LOC_BY_EXTENSION));
		if (isPreprocessor) {
			addChild(new LOCFilterNode(LOC_BY_FEATURE, fileFeatureLOCMapper, project, LOC_BY_FEATURE));
		
			int allLOC = fileFeatureLOCMapper.allLinesOfCode(); //TODO check allLinesOfCode for correctness
			int preProcessorLOC = fileFeatureLOCMapper.getFeatureCount()*2; //TODO getFeatureCount() isn't always right! Example: elif , x1 && x2, if you use the same feature more times it will not counted			
			int variableLOC = fileFeatureLOCMapper.getCompleteFeatureLOC();
			int nonVariableCode = allLOC - (preProcessorLOC + variableLOC) ;
			
			System.out.println("all: " +fileFeatureLOCMapper.allLinesOfCode());
			System.out.println("Variable LOC :" + variableLOC);
			System.out.println("ppLOC: " + preProcessorLOC);
			
			addChild(new LOCFilterNode(NON_VARIABLE_LOC + SEPARATOR + nonVariableCode, fileFeatureLOCMapper, project, NON_VARIABLE_LOC));
			
			if(variableLOC == 0) {
				addChild(new LOCFilterNode(VARIABLE_LOC +  VARIABLE_LOC_WARNING  + SEPARATOR + variableLOC, fileFeatureLOCMapper, project, VARIABLE_LOC));
			} else {
				addChild(new LOCFilterNode(VARIABLE_LOC  + SEPARATOR + variableLOC, fileFeatureLOCMapper, project, VARIABLE_LOC));
			}
			
			addChild(new LOCFilterNode(PP_LOC + SEPARATOR + preProcessorLOC, fileFeatureLOCMapper, project, PP_LOC));			
		}
	}

}
