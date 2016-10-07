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

import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;
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

	LOCNode(String description, boolean isPreprocessor) {
		super(description);
		this.fileFeatureLOCMapper = null;
		this.isPreprocessor = isPreprocessor;
	}
	
	public LOCNode(String description, FileFeatureLOCMapper ffLOCMapper, boolean isPreprocessor) {
		super(description);
		this.fileFeatureLOCMapper = ffLOCMapper;
		this.isPreprocessor = isPreprocessor;
	}

	@Override
	protected void initChildren() {
		addChild(new LOCFilterNode(LOC_BY_EXTENSION, fileFeatureLOCMapper));
		if (isPreprocessor) {
			addChild(new LOCFilterNode(LOC_BY_FEATURE, fileFeatureLOCMapper));
			int locWithoutFeat = fileFeatureLOCMapper.locWithoutFeatures();
			int preProcessorLOC = fileFeatureLOCMapper.getFeatures().size()*2;
			
			int nonVariableCode = locWithoutFeat - preProcessorLOC;
			int VariableLOC = fileFeatureLOCMapper.allLinesOfCode() - locWithoutFeat + preProcessorLOC;
			
			addChild(new Parent("Non-Variable lines of code", nonVariableCode));
			if(VariableLOC == 0) {
				addChild(new Parent("Variable lines of code (includes PreProcessor statements) (This may not be accurate.)", VariableLOC));
			} else {
				addChild(new Parent("Variable lines of code (includes PreProcessor statements)", VariableLOC));
			}
			addChild(new Parent("Preprocessor lines of code", preProcessorLOC ));
		}
	}

}
