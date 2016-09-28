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
package de.ovgu.featureide.fm.core.io.xml;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.FileNotFoundException;

import org.junit.Test;

import de.ovgu.featureide.common.Commons;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * TODO description
 * 
 * @author root
 */
public class TXMLFeatureModelReaderWriter {
	
	@Test
	public void testFeatureCollapsed() throws FileNotFoundException, UnsupportedModelException {
		IFeatureModel fmOrig = Commons.loadFeatureModelFromFile("basic.xml", Commons.FEATURE_MODEL_TESTFEATUREMODELS_PATH_REMOTE, Commons.FEATURE_MODEL_TESTFEATUREMODELS_PATH_LOCAL_CLASS_PATH);
		IFeatureModel fmCollapsed = Commons.loadFeatureModelFromFile("basic_collapsed.xml", Commons.FEATURE_MODEL_TESTFEATUREMODELS_PATH_REMOTE, Commons.FEATURE_MODEL_TESTFEATUREMODELS_PATH_LOCAL_CLASS_PATH);
		IFeatureModel fmNotCollapsed = Commons.loadFeatureModelFromFile("basic_not_collapsed.xml", Commons.FEATURE_MODEL_TESTFEATUREMODELS_PATH_REMOTE, Commons.FEATURE_MODEL_TESTFEATUREMODELS_PATH_LOCAL_CLASS_PATH);
		
		for (IFeature origF : fmOrig.getFeatures()) {
				IFeature newF = fmCollapsed.getFeature(origF.getName());
				if (newF == null) {
					fail();
				} else {
					assertEquals("Feature: " + origF.getName(), !origF.getStructure().isCollapsed(), fmCollapsed.getFeature(origF.getName()).getStructure().isCollapsed());
				}
		}
		
		for (IFeature origF : fmOrig.getFeatures()) {
				IFeature newF = fmNotCollapsed.getFeature(origF.getName());
				
				if (newF == null) {
					fail();
				} else {
					assertEquals("Feature: " + origF.getName(), origF.getStructure().isCollapsed(), fmNotCollapsed.getFeature(origF.getName()).getStructure().isCollapsed());
				}
		}
	}
	
}
