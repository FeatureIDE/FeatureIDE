/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.configuration;

import static org.junit.Assert.assertTrue;

import org.junit.Before;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FeatureModelFactory;
import de.ovgu.featureide.fm.core.io.IFeatureModelReader;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.guidsl.GuidslReader;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;

/**
 * Abstract class that can be used for tests on configurations. 
 * Each set of configuration tests that is performed on the same model is defined 
 * in its own subclass.
 * 
 * @author Fabian Benduhn
 */
public abstract class AbstractConfigurationTest {

	public static IFeatureModel fm; 

	@Before
	public void setModel(){
		fm = loadModel();
	}
	
	/**
	 * This method is used by setModel() to initialize 
	 * the feature model before each test case. 
	 * For basic string input use methods loadGUIDSL or loadXML.
	 * For file input use any FeatureModelReader.
	 * 
	 * @return the FeatureModel used in this test class
	 */
	 
	abstract IFeatureModel loadModel();
	
	protected static IFeatureModel loadGUIDSL(String grammar) {
		IFeatureModel fm = FeatureModelFactory.getInstance().createFeatureModel();
		IFeatureModelReader reader = new GuidslReader(fm);
		try {
			reader.readFromString(grammar);
		} catch (UnsupportedModelException e) {
			assertTrue(false);
		}
		return fm;
	}

	/**
	 * shorthand to define a featuremodel by a String and load it into a FeatureModel
	 * @param fmXml XML representation of the feature model (without constraints -> part within first  <struct> )
	 * @param constraintsXml XML representation of the constraints (part within  <constraints> ).
	 *  	  
	 * @return
	 */
	protected static IFeatureModel loadXML(String fmXml,String constraintsXml) {
		String xml = "<featureModel><struct>" + fmXml;
		xml += "</struct>";
		if(constraintsXml!=null){	
			xml += "<constraints>";
			xml += constraintsXml + "</constraints>";
		}
		xml += "</featureModel>";
		IFeatureModel fm = FeatureModelFactory.getInstance().createFeatureModel();
		IFeatureModelReader reader = new XmlFeatureModelReader(fm);
		try {
			reader.readFromString(xml);
		} catch (UnsupportedModelException e) {
			assertTrue(false);
		}
		return fm;
	}
	/**
	 * shorthand to define a featuremodel by a String and load it into a FeatureModel
	 * @param fmXml XML representation of the feature model (without constraints -> part within first  <struct> )
	 * @param constraintsXml XML representation of the constraints (part within  <constraints> ).
	 *  	  
	 * @return
	 */
	protected static IFeatureModel loadXML(String fmXml) {
		return loadXML(fmXml,null);
	}
	/**
	 * 
	 */
	public AbstractConfigurationTest() {
		super();
	}

}
