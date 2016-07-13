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
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.List;

import org.junit.Test;
import org.prop4j.And;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.NodeWriter;
import org.prop4j.Not;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.conversion.ComplexConstraintConverter.Option;
import de.ovgu.featureide.fm.core.editing.Comparison;
import de.ovgu.featureide.fm.core.editing.ModelComparator;
import de.ovgu.featureide.fm.core.io.FeatureModelReaderIFileWrapper;
import de.ovgu.featureide.fm.core.io.FeatureModelWriterIFileWrapper;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.fama.FAMAWriter;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelWriter;
//import de.ovgu.featureide.fm.ui.FMUIPlugin;

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
		//IFeature D = factory.createFeature(fm, "D");
		
		A.getStructure().setMandatory(false);
		B.getStructure().setMandatory(false);
		C.getStructure().setMandatory(false);
		
		A.getStructure().setAbstract(false);
		B.getStructure().setAbstract(false);
		C.getStructure().setAbstract(false);
		//D.getStructure().setMandatory(false);
		
		fm.getStructure().getRoot().addChild(A.getStructure());
		fm.getStructure().getRoot().addChild(B.getStructure());
		fm.getStructure().getRoot().addChild(C.getStructure());
		//fm.getStructure().getRoot().addChild(D.getStructure());
		fm.getStructure().getRoot().setAnd();
		
		Node n1 = new Or(A, B);
		Node n2 = new Or(B, C);
		//Node n3 = new Implies(new And(new Or(A,B), D), new Not(C));
		
		IConstraint c1 = factory.createConstraint(fm, n1);
		IConstraint c2 = factory.createConstraint(fm, n2);
		//IConstraint c3 = factory.createConstraint(fm, n3);
	    fm.addConstraint(c1);
		fm.addConstraint(c2);
		//fm.addConstraint(c3);
	}
	
	/*
	 * Check whether our converter recognizes simple constraints.
	 */
	@Test
	public void testIsSimpleConstraint() throws UnsupportedModelException {
		Node[] simpleNodes = new Node[] {
				 				new Implies("f", "g"),
				 				new Or("f",new Not("g")), 
				 				new Or(new Not("f"),"g"), 
				 				new Or(new Not("f"),new Not("g")), 
				 				new Implies("f", new Not(new Not("g"))),
				 				new Implies("f", new Not("g")),
				 				new Implies("f", new Literal("g")),
				 				new Implies("f", new Not(new Literal("g"))),
				 				new Implies(new Literal("f"), new Not("g")),
				 				new Implies(new Literal("f"), new Literal("g")),
				 				new Implies(new Literal("f"), new Not(new Literal("g")))};

		boolean result = true;
		for (Node node : simpleNodes) {
			result &= ComplexConstraintConverter.isSimple(node);
 		}	

		assertTrue(result);
	}
	
	/*
	 * Check whether our converter recognizes simple constraints.
	 */
	@Test
	public void testIsComplexConstraint() throws UnsupportedModelException {
		Node[] complexNodes = new Node[] {
 				new Implies(new Not("f"), "g"),
 				new Implies("f", new And("g", "h")),
 				new Implies("f", new Or("g", "h")),
 				new Or("f", "g"),
 				new And("f", "g")};

		boolean result = true;
		for (Node node : complexNodes) {
			result &= ComplexConstraintConverter.isComplex(node);
 		}	

		assertTrue(result);
	}
	
	/*
	 * Conversion should preserve semantics.
	 */
//	@Test
//	public void testNNFConversion() throws UnsupportedModelException {
//		ComplexConstraintConverter converter = new ComplexConstraintConverter();
//		IFeatureModel resultFM = converter.convert(fm, new NNFConverter());
//		
//		assertEquals(Comparison.REFACTORING, comparator.compare(fm, resultFM));	
//	}
	
	/*
	 * Conversion should preserve semantics.
	 */
//	@Test
//	public void testCNFConversion() throws UnsupportedModelException {
//		ComplexConstraintConverter converter = new ComplexConstraintConverter();
//		IFeatureModel resultFM = converter.convert(fm, new CNFConverter(), Option.COHERENT);
//		comparator.compare(fm, resultFM);
//			
//		System.out.println(fm.getFeatureOrderList());
//		System.out.println(resultFM.getFeatureOrderList());
//		System.out.println(comparator.getAddedFeatures());
//		System.out.println(comparator.getDeletedFeatures());
//		assertEquals(Comparison.REFACTORING, comparator.getResult());
//	}
	
}
