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
package de.ovgu.featureide.fm.core.conversion;

import static org.junit.Assert.assertEquals;

import org.junit.Test;
import org.prop4j.Node;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.editing.Comparison;
import de.ovgu.featureide.fm.core.editing.ModelComparator;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * TODO description
 * 
 * @author Alexander Knueppel
 */
public class TComplexConstraintConverter {
	
	private static final ModelComparator comparator = new ModelComparator(10000);
	private static final IFeatureModelFactory factory = FMFactoryManager.getFactory();
	private static IFeatureModel fm;
	
	static {
		// setup a test model
        fm = factory.createFeatureModel(); 
        final IFeature root = factory.createFeature(fm, "root");
        
		fm.addFeature(root);
		fm.getStructure().setRoot(root.getStructure());
		
		IFeature A = factory.createFeature(fm, "A");
		IFeature B = factory.createFeature(fm, "B");
		IFeature C = factory.createFeature(fm, "C");
		
		A.getStructure().setMandatory(false);
		B.getStructure().setMandatory(false);
		C.getStructure().setMandatory(false);
		
		fm.getStructure().getRoot().addChild(A.getStructure());
		fm.getStructure().getRoot().addChild(B.getStructure());
		fm.getStructure().getRoot().addChild(C.getStructure());
		
		fm.getStructure().getRoot().setAnd();
		
		Node n1 = new Or(A, B);
		Node n2 = new Or(B, C);
		
		IConstraint c1 = factory.createConstraint(fm, n1);
		IConstraint c2 = factory.createConstraint(fm, n2);
		
	    fm.addConstraint(c1);
		fm.addConstraint(c2);
	}
	
	/*
	 * Conversion should preserve semantics.
	 */
	@Test
	public void testConversion() throws UnsupportedModelException {
		ComplexConstraintConverter converter = new ComplexConstraintConverter();
		IFeatureModel resultFM = converter.convert(fm, null);
		
		assertEquals(Comparison.REFACTORING, comparator.compare(fm, resultFM));	
	}
}
