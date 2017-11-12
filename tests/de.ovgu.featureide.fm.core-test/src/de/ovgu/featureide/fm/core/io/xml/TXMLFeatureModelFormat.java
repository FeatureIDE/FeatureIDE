/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.io.xml;

import static org.junit.Assert.assertEquals;

import java.io.FileNotFoundException;

import org.junit.Test;
import org.prop4j.Node;
import org.prop4j.Or;

import de.ovgu.featureide.Commons;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.TAbstractFeatureModelReaderWriter;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * Class to test the collapse feature of XmlFeatureModelFormat.java
 *
 * @author Christopher Sontag
 * @author Maximilian Kühl
 * @author Marlen Bernier
 * @author Dawid Szczepanski
 */
public class TXMLFeatureModelFormat extends TAbstractFeatureModelReaderWriter {

	/**
	 * @param file
	 * @throws UnsupportedModelException
	 */

	public TXMLFeatureModelFormat(IFeatureModel fm, String s) throws UnsupportedModelException {
		super(fm, s);

	}

	@Test
	public void testConstraintDescription() throws FileNotFoundException, UnsupportedModelException {
		String constraintdescriptionFromXml = "";

		final IFeatureModel fm = Commons.loadTestFeatureModelFromFile("constraintDescriptionTest.xml");
		assertEquals(1, fm.getConstraints().size());

		for (IConstraint constraint : fm.getConstraints()) {
			constraintdescriptionFromXml = constraint.getDescription();
			assertEquals(constraintdescriptionFromXml, "Test Description");

		}
	}

	@Test
	public void testConstraintDescriptionTwoRules() throws FileNotFoundException, UnsupportedModelException {
		String constraintdescriptionFromXml = "";

		final IFeatureModel fm = Commons.loadTestFeatureModelFromFile("constraintDescriptionTwoRulesTest.xml");
		assertEquals(2, fm.getConstraints().size());
		int i = 1;
		for (IConstraint constraint : fm.getConstraints()) {
			constraintdescriptionFromXml = constraint.getDescription();
			assertEquals(constraintdescriptionFromXml, "Test Description " + i);
			i++;

		}
	}

	private IFeatureModel prepareFeatureModel() {
		final IFeatureModelFactory factory = FMFactoryManager.getDefaultFactory();

		// setup a test model
		newFm = factory.createFeatureModel();
		final IFeature root = factory.createFeature(newFm, "root");

		newFm.addFeature(root);
		newFm.getStructure().setRoot(root.getStructure());

		final IFeature A = factory.createFeature(newFm, "A");
		final IFeature B = factory.createFeature(newFm, "B");
		final IFeature C = factory.createFeature(newFm, "C");

		A.getStructure().setMandatory(false);
		B.getStructure().setMandatory(false);
		C.getStructure().setMandatory(false);

		A.getStructure().setAbstract(false);
		B.getStructure().setAbstract(false);
		C.getStructure().setAbstract(false);

		newFm.getStructure().getRoot().addChild(A.getStructure());
		newFm.getStructure().getRoot().addChild(B.getStructure());
		newFm.getStructure().getRoot().addChild(C.getStructure());
		newFm.getStructure().getRoot().setAnd();

		final Node n1 = new Or(A, B);
		final Node n2 = new Or(B, C);

		final IConstraint c1 = factory.createConstraint(newFm, n1);
		c1.setDescription("Test Write Description 1");

		final IConstraint c2 = factory.createConstraint(newFm, n2);
		c2.setDescription("Test Write Description 2");
		newFm.addConstraint(c1);
		newFm.addConstraint(c2);

		return newFm;
	}

	@Test
	public void testConstraintDescriptionWrite() throws FileNotFoundException, UnsupportedModelException {
		IFeatureModel newFm = this.prepareFeatureModel();

		String constraintdescriptionFromXml = "";
		int i = 1;
		for (IConstraint constraint : newFm.getConstraints()) {
			constraintdescriptionFromXml = constraint.getDescription();
			assertEquals(constraintdescriptionFromXml, "Test Write Description " + i);
			i++;

		}
	}

	@Test
	public void testConstraintWithoutDescription() throws FileNotFoundException, UnsupportedModelException {
		String constraintdescriptionFromXml = "";

		final IFeatureModel fm = Commons.loadTestFeatureModelFromFile("basic.xml");
		assertEquals(1, fm.getConstraints().size());

		for (IConstraint constraint : fm.getConstraints()) {
			constraintdescriptionFromXml = constraint.getDescription();
			assertEquals(constraintdescriptionFromXml, "");

		}
	}

	/*
	 * @see de.ovgu.featureide.fm.core.io.TAbstractFeatureModelReaderWriter#getFormat()
	 */
	@Override
	protected IFeatureModelFormat getFormat() {
		return new XmlFeatureModelFormat();
	}

}
