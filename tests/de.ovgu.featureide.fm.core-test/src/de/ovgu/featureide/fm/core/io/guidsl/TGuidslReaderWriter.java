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
package de.ovgu.featureide.fm.core.io.guidsl;

import static org.junit.Assert.assertTrue;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.IFeatureModelReader;
import de.ovgu.featureide.fm.core.io.IFeatureModelWriter;
import de.ovgu.featureide.fm.core.io.TAbstractFeatureModelReaderWriter;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * Test class for GuidslReader
 * 
 * @author Fabian Benduhn
 */
public class TGuidslReaderWriter extends TAbstractFeatureModelReaderWriter{
	/**
	 * @param file
	 * @throws UnsupportedModelException 
	 */
	public TGuidslReaderWriter(FeatureModel fm, String s) throws UnsupportedModelException {
		super(fm, s);
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.io.TAbstractFeatureModelReaderWriter#getWriter()
	 */
	@Override
	protected IFeatureModelWriter getWriter(FeatureModel fm) {
		return new GuidslWriter(fm);
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.io.TAbstractFeatureModelReaderWriter#getReader()
	 */
	@Override
	protected IFeatureModelReader getReader(FeatureModel fm) {
		return new GuidslReader(fm);
	}

	//guidsl does not save concrete compound features
	@Override
	public void testFeatureConcrete(){
		for (Feature origF : origFm.getFeatures()) {
			if (!origF.isConcrete()&&origF.isConcrete()) {
				Feature newF = newFm.getFeature(origF.getName());
				if (newF == null){
					//fail("Feature " + origF.getName() + " cannot be found");
				}	else {
					assertTrue(failureMessage+origF, newFm
							.getFeature(origF.getName()).isConcrete());
				}
			}
		}
	}

	@Override
	public void testDescription() {
		// description not implemented
	}
	
}
