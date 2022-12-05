/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.examples.featureattributes;

import java.nio.file.Path;
import java.nio.file.Paths;

import de.ovgu.featureide.fm.attributes.FMAttributesLibrary;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.BooleanFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.base.impl.StringFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.init.FMCoreLibrary;
import de.ovgu.featureide.fm.core.init.LibraryManager;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;

/**
 * An example usage of the FeatureIDE attributes library.
 *
 * @author Chico Sundermann
 */
public class FeatureAttributes {

	public static void main(String[] args) {
		
		ExtendedFeatureModel featureModel = performSetup();
		
		readAttributeValues(featureModel);
		
		addAttributeValues(featureModel);
	}
	
	// -------------------- Structure Methods --------------------
	
	private static ExtendedFeatureModel performSetup() {
		// Register required libraries
		LibraryManager.registerLibrary(FMCoreLibrary.getInstance());
		LibraryManager.registerLibrary(FMAttributesLibrary.getInstance());
		
		// load extended feature model
		final Path path = Paths.get("sandwich.xml");
		return (ExtendedFeatureModel) FeatureModelManager.load(path);
	}
	
	private static void addAttributeValues(ExtendedFeatureModel featureModel) {
		IFeature ham = featureModel.getFeature("Ham");
		// Create new attribute
		IFeatureAttribute supplier = new StringFeatureAttribute(ham, "supplier", "", "Farmer Mike", false, false);
		
		// Append attribute
		addAttribute(ham, supplier);
		printAttributes(ham, "Attributes of Ham after change");
		
		// Create recursive attribute; a recursive attribute is added to all descendants of the feature
		IFeature bread = featureModel.getFeature("Bread");
		IFeatureAttribute gluten = new BooleanFeatureAttribute(bread, "gluten", "", false, true, false);
		addAttribute(bread, gluten);
		
		// Add value for recursive attributes of descendants
		IFeature flatbread = featureModel.getFeature("Flatbread");
		changeAttributesValue("gluten", flatbread, true);
		printAttributes(flatbread, "Attributes of Flatbread with new recursive attribute gluten");
	}
	
	private static void readAttributeValues(ExtendedFeatureModel featureModel) {
		// Read attribute values
		IFeature ham = featureModel.getFeature("Ham");
		printAttributes(ham, "Attributes of Ham before Changes");
	}
	
	
	
	// -------------------- Support Methods --------------------
	
	private static void printAttributes(IFeature feat, String header) {
		if (feat instanceof ExtendedFeature) {
			ExtendedFeature ext = (ExtendedFeature) feat;
			System.out.println("\n" + header);
			for (IFeatureAttribute attribute : ext.getAttributes()) {
				System.out.println(attribute.getName() + ":" + attribute.getValue() + attribute.getUnit());
			}
		} else {
			System.out.println("Not an extended feature!");
		}
	}
	
	
	private static void addAttribute(IFeature feat, IFeatureAttribute att) {
		if (feat instanceof ExtendedFeature) {
			ExtendedFeature ext = (ExtendedFeature) feat;
			ext.addAttribute(att);
			if (att.isRecursive()) {
				att.addRecursiveAttributes();
			}
		}
	}
	
	private static void changeAttributesValue(String attributeName, IFeature feat, Object newValue) {
		if (feat instanceof ExtendedFeature) {
			ExtendedFeature ext = (ExtendedFeature) feat;
			for (IFeatureAttribute att : ext.getAttributes()) {
				if (att.getName().equals(attributeName)) {
					att.setValue(newValue);
				}
			}
		}
	}

}
